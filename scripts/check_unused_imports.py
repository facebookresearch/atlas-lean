#!/usr/bin/env python3
"""Report the imports that a change adds and that agitate finds unused.

agitate (https://github.com/thorimur/agitate) reimplements `lake shake` by
reading `.olean` files directly. This script runs it on the Lean files of the
production libraries that `BASE...HEAD` adds or modifies, which must be built
already (`python3 scripts/lean_changes.py build`), and keeps its `remove`
suggestions on the import lines that the change adds. Imports that were already
in a file are not reported, and neither are `add` suggestions.

    python3 scripts/check_unused_imports.py --base origin/main --agitate-dir DIR [--report-only]

DIR is a checkout of agitate at the commit that .github/workflows/linters.yml
pins, built with `lake build agitate agitate-nonmodule` for the toolchain in
lean-toolchain (`.olean` files are specific to a toolchain); it defaults to
$AGITATE_DIR. Files that use the module system are checked with `agitate
--keep-public --add-public --keep-implied --keep-prefix`: a public import is
removed only where the file's other public imports already export it, so that
no importer of the file can break, and imports that other imports imply, or
that re-export what the file uses, are kept. Other files are checked with
`agitate-nonmodule --keep-implied --keep-prefix`; their imports are re-exported,
so their importers can rely on an import that the file itself does not use.

When agitate also suggests adding imports to a file, the finding names them. A
removed import may be used through one of those smaller modules, or they may
only be modules that agitate keeps wherever they were reachable, such as those
that declare simp sets or attributes.

Exit 1 if a finding is kept (0 with --report-only), 0 if none, 2 if agitate
cannot run or skips a changed file whose header it cannot read (whatever it
found in the others). In GitHub Actions each finding also annotates its line
and the job summary counts them.

Run the tests with: python3 -m unittest discover -s scripts -p test_check_unused_imports.py
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_changes import (ROOT, ChangedFile, add_common_arguments, annotation, changed_files,
                          guarded, in_actions, inert, relative, unnameable, write_summary)

# With --gh-style, agitate prints one of these for each import that it would remove,
# with a 1-based column.
UNUSED = re.compile(r"^(?P<file>\S.*?\.lean):(?P<line>\d+):(?P<col>\d+): warning: unused import\b")
# It also prints each file that it would edit, followed by its `remove #[...]` and
# `add #[...]` lists.
FILE = re.compile(r"^(?P<file>\S.*?\.lean):$")
ADD = re.compile(r"^  add #\[(?P<imports>.*)\]$")
# agitate exits 1 both when it suggests edits and when it fails, for example on a
# missing .olean file; a failure prints one of these to stderr.
FAILED = re.compile(r"^(?:uncaught exception|error|PANIC|INTERNAL PANIC)\b", re.MULTILINE)
# What agitate prints to stdout when it cannot read a changed file's header: Lean's parse errors
# and "parse errors in file", "error: failed to find source file for M", or an I/O error. It then
# skips that file, and can exit 0.
SKIPPED = re.compile(r"^(?:error: .*|\S.*?:\d+:\d+: error: .*|parse errors in file)$"
                     r"|^.*\(error code: \d+[,)].*$", re.MULTILINE)

# Keep every public import that other public imports do not already export, so
# that no importer can break; keep imports that other imports imply, and a parent
# module rather than the submodules of it that a file uses (as Mathlib imports
# `Mathlib.Tactic.Linarith`), so that only imports that nothing needs are reported.
MODULE_FLAGS = ("--keep-public", "--add-public", "--keep-implied", "--keep-prefix")
NONMODULE_FLAGS = ("--keep-implied", "--keep-prefix")


@dataclass
class Header:
    """Whether a file uses the module system, and its import statements by the 1-based line and
    column at which each starts (Lean accepts several on one line)."""

    is_module: bool = False
    imports: dict[tuple[int, int], str] = field(default_factory=dict)

    @property
    def lines(self) -> set[int]:
        return {line for line, _ in self.imports}


def tokens(text: str):
    """The (token, line, column) triples of a Lean file's start, without comments; line and
    column are 1-based."""
    i, n, line, line_start = 0, len(text), 1, 0
    while i < n:
        if text[i] == "\n":
            line += 1
            i += 1
            line_start = i
        elif text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    if text[i] == "\n":
                        line, line_start = line + 1, i + 1
                    i += 1
        else:
            start = i
            while i < n and not text[i].isspace() and not text.startswith(("--", "/-"), i):
                i += 1
            yield text[start:i], line, start - line_start + 1


def header(text: str) -> Header:
    """The `module` keyword and the `[public] [meta] import [all] M` lines of a file."""
    result = Header()
    words: list[str] = []
    start: tuple[int, int] | None = None
    for tok, line, col in tokens(text):
        if not words and not result.imports and not result.is_module and tok == "module":
            result.is_module = True
        elif not words and not result.imports and tok == "prelude":
            continue
        elif tok in ("public", "meta") and "import" not in words:
            words, start = words + [tok], start or (line, col)
        elif tok == "import" and "import" not in words:
            words, start = words + [tok], start or (line, col)
        elif tok == "all" and words and words[-1] == "import":
            words.append(tok)
        elif words and words[-1] in ("import", "all") and start is not None:
            result.imports[start] = " ".join([*words, tok])
            words, start = [], None
        else:
            break
    return result


@dataclass(frozen=True)
class Removal:
    """An import that agitate would remove, at a 1-based line and column."""

    path: str
    line: int
    col: int


def parse_output(text: str, cwd: Path = ROOT) -> tuple[list[Removal], dict[str, list[str]]]:
    """agitate's removals (from --gh-style lines) and its `add` lists, by file."""
    removals: list[Removal] = []
    adds: dict[str, list[str]] = {}
    current: str | None = None
    for line in text.splitlines():
        if match := UNUSED.match(line):
            removals.append(Removal(relative(match.group("file"), cwd), int(match.group("line")),
                                    int(match.group("col"))))
        elif match := FILE.match(line):
            current = relative(match.group("file"), cwd)
        elif (match := ADD.match(line)) and current is not None:
            adds.setdefault(current, []).extend(
                item.strip() for item in match.group("imports").split(",") if item.strip())
    return list(dict.fromkeys(removals)), adds


def read_source(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8", errors="replace")


def agitate_problem(agitate_dir: Path, cwd: Path = ROOT) -> str | None:
    """Why the agitate build in `agitate_dir` cannot check this repository, if it cannot."""
    for tool in ("agitate", "agitate-nonmodule"):
        if not (agitate_dir / ".lake" / "build" / "bin" / tool).is_file():
            return (f"{agitate_dir}/.lake/build/bin/{tool} does not exist; build it with "
                    f"`lake build agitate agitate-nonmodule` in {agitate_dir}")
    try:
        theirs = (agitate_dir / "lean-toolchain").read_text().strip()
        ours = (cwd / "lean-toolchain").read_text().strip()
    except OSError as error:
        return f"cannot compare the toolchains: {error}"
    if theirs != ours:
        return (f"agitate in {agitate_dir} is built for {theirs}, but this repository uses {ours}; "
                f"pin an agitate commit for {ours} in .github/workflows/linters.yml")
    return None


def run_agitate(binary: Path, flags: tuple[str, ...], modules: list[str]
                ) -> subprocess.CompletedProcess:
    only = [arg for module in modules for arg in ("--only", module)]
    return subprocess.run([str(binary), *flags, "--gh-style", *only, *modules], cwd=ROOT,
                          capture_output=True, text=True)


@guarded
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    add_common_arguments(parser)
    parser.add_argument("--agitate-dir", default=os.environ.get("AGITATE_DIR"),
                        help="a built checkout of agitate (default: $AGITATE_DIR)")
    args = parser.parse_args()

    files = changed_files(args.base)
    if not files:
        print("No Lean file of the production libraries is added or modified.")
        return 0
    targets: dict[str, tuple[ChangedFile, Header]] = {}
    skipped_files = unnameable(files)
    for file in files:
        if file in skipped_files:
            continue
        head = header(read_source(file.path))
        if head.lines & file.added_lines:
            targets[file.path] = (file, head)
    if not targets:
        print("No changed Lean file of the production libraries adds an import.")
        return 0
    if not args.agitate_dir:
        print("Give the agitate build with --agitate-dir or AGITATE_DIR.", file=sys.stderr)
        return 2
    agitate_dir = Path(args.agitate_dir)
    problem = agitate_problem(agitate_dir)
    if problem:
        print(problem, file=sys.stderr)
        return 2

    print(f"Checking the imports that {len(targets)} changed Lean file(s) add.")
    removals: list[Removal] = []
    adds: dict[str, list[str]] = {}
    skipped: list[str] = []
    for tool, is_module, flags in (("agitate", True, MODULE_FLAGS),
                                   ("agitate-nonmodule", False, NONMODULE_FLAGS)):
        modules = [file.lean_module for file, head in targets.values()
                   if head.is_module == is_module]
        if not modules:
            continue
        result = run_agitate(agitate_dir / ".lake" / "build" / "bin" / tool, flags, modules)
        if result.returncode not in (0, 1) or FAILED.search(result.stderr):
            print(inert(result.stdout + result.stderr), file=sys.stderr)
            print(f"{tool} did not run on the changed files.", file=sys.stderr)
            return 2
        skipped += [match.group(0) for match in SKIPPED.finditer(result.stdout)]
        found, added = parse_output(result.stdout)
        removals += found
        adds.update(added)

    kept = [r for r in removals if r.path in targets and r.line in targets[r.path][0].added_lines]
    level = "warning" if args.report_only else "error"
    titles: Counter[str] = Counter()
    for r in kept:
        statement = targets[r.path][1].imports.get((r.line, r.col), "this import")
        title = "unused import"
        message = (f"agitate finds `{statement}` unused here. Remove it, or mark it "
                   f"`-- shake: keep` if it is needed in a way that .olean files do not "
                   f"record (such as `open` of a namespace).")
        if adds.get(r.path):
            title = "unused import, with replacements"
            smaller = ", ".join(f"`{item}`" for item in adds[r.path])
            message += (f" agitate also suggests importing {smaller}: if the file does not build "
                        f"without this import, import those smaller modules instead.")
        titles[title] += 1
        if in_actions():
            print(annotation(level, r.path, r.line, title, message, r.col))
        print(inert(f"{r.path}:{r.line}: {title}: {message}"))
    if kept:
        rows = "".join(f"| {title} | {count} |\n" for title, count in titles.most_common())
        write_summary(f"### Imports on added lines that agitate would remove\n\n"
                      f"| Finding | Imports |\n|---|---:|\n{rows}\n")
        print(f"{len(kept)} added import(s) that agitate would remove.")
    if skipped:
        # agitate checked the other files, but not this one: the check is incomplete.
        print(inert("\n".join(skipped)), file=sys.stderr)
        print("agitate could not read the header of a changed file and skipped it, so the check "
              "is incomplete.", file=sys.stderr)
        return 2
    if kept:
        return 0 if args.report_only else 1
    print("agitate would remove none of the added imports.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
