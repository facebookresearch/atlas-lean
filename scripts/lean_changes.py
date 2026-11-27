#!/usr/bin/env python3
"""The Lean files that a change adds or modifies, and the lines it adds to them.

The linter checks in CI (.github/workflows/linters.yml) report a finding only on
code that a pull request adds, so existing code does not fail a check whatever
its style. This module reads the change from `git diff BASE...HEAD`, the way
scripts/check_copyright.py does, and writes the temporary aggregator modules
that the Lean tools need.

    python3 scripts/lean_changes.py build --base origin/main

builds the Lean files of the production libraries that the change adds or
modifies, through those aggregators (exit 0 when they build, 1 when they do not,
2 when the aggregators cannot be written).

Run the tests with: python3 -m unittest discover -s scripts -p test_lean_changes.py
"""

from __future__ import annotations

import argparse
import contextlib
import functools
import os
import re
import subprocess
import sys
from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The libraries that lakefile.toml builds with Mathlib's standard linter set.
PRODUCTION_LIBRARIES = ("MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt")

# Each library globs its submodules (`MathlibExt.+`), so an aggregator must be
# one of them to build. It is untracked, and removed when the check ends.
AGGREGATOR = "LintChanged"

HUNK = re.compile(r"^@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")

# Git quotes a path that holds a control character, `"` or `\` (and, unless
# core.quotePath is false, a non-ASCII byte) in C style: "a\tb\303\251".
ESCAPES = {"a": 7, "b": 8, "t": 9, "n": 10, "v": 11, "f": 12, "r": 13, '"': 34, "\\": 92}


@dataclass(frozen=True)
class ChangedFile:
    """A Lean file of the change: its path, git status letter and added lines.

    `old_path` is the file's path at the base when the change renames or copies it.
    """

    path: str
    status: str
    added_lines: frozenset[int]
    old_path: str | None = None

    @property
    def library(self) -> str:
        return self.path.split("/", 1)[0]

    @property
    def module(self) -> str:
        return self.path.removesuffix(".lean").replace("/", ".")

    @property
    def base_path(self) -> str | None:
        """The file's path at the base, or `None` when the change adds it."""
        if self.status == "A":
            return None
        return self.old_path or self.path


class AggregatorError(Exception):
    """An aggregator module cannot be written, because a file of that name exists."""


class GitError(Exception):
    """git cannot read the change, for example because the base ref does not exist."""


def unquote(path: str) -> str:
    """A path from a diff header, with git's C-style quoting undone."""
    if len(path) < 2 or not (path.startswith('"') and path.endswith('"')):
        return path
    out = bytearray()
    body = path[1:-1]
    i = 0
    while i < len(body):
        char = body[i]
        if char != "\\":
            out += char.encode("utf-8")
            i += 1
        elif body[i + 1 : i + 4].isdigit() and len(body[i + 1 : i + 4]) == 3:
            out.append(int(body[i + 1 : i + 4], 8))
            i += 4
        else:
            out.append(ESCAPES.get(body[i + 1 : i + 2], ord(body[i + 1 : i + 2] or "\\")))
            i += 2
    return out.decode("utf-8", errors="surrogateescape")


def parse_diff(text: str) -> dict[str, frozenset[int]]:
    """Map each file of a `git diff --unified=0` to the line numbers it adds.

    A hunk's body is read by the line counts in its `@@` header, so an added
    line that itself starts with `++ ` (shown as `+++ `) is never taken for the
    next file's header.
    """
    added: dict[str, set[int]] = {}
    path: str | None = None
    old_left = new_left = 0
    new_line = 0
    for line in text.split("\n"):
        if old_left > 0 or new_left > 0:
            tag = line[:1]
            if tag == "\\":
                continue  # "\ No newline at end of file" belongs to the line before
            if tag == "+" and new_left > 0:
                if path is not None:
                    added[path].add(new_line)
                new_line += 1
                new_left -= 1
                continue
            if tag == "-" and old_left > 0:
                old_left -= 1
                continue
            if tag == " " and old_left > 0 and new_left > 0:
                old_left -= 1
                new_left -= 1
                new_line += 1
                continue
            old_left = new_left = 0  # a malformed hunk: read the line as a header
        if line.startswith("diff --git "):
            path = None
        elif line.startswith("+++ "):
            target = unquote(line[4:].rstrip("\t"))
            path = target[2:] if target.startswith("b/") else None
            if path is not None:
                added.setdefault(path, set())
        elif (match := HUNK.match(line)) and path is not None:
            old_left = int(match.group(1)) if match.group(1) is not None else 1
            new_line = int(match.group(2))
            new_left = int(match.group(3)) if match.group(3) is not None else 1
    return {path: frozenset(lines) for path, lines in added.items()}


def parse_name_status(text: str) -> dict[str, tuple[str, str | None]]:
    """Map each path of a `git diff --name-status -z` to its status letter and old path."""
    fields = text.split("\0")
    statuses: dict[str, tuple[str, str | None]] = {}
    i = 0
    while i < len(fields) and fields[i]:
        letter = fields[i][0]
        if letter in "RC":
            statuses[fields[i + 2]] = (letter, fields[i + 1])
            i += 3
        else:
            statuses[fields[i + 1]] = (letter, None)
            i += 2
    return statuses


def git(args: Sequence[str], cwd: Path) -> str:
    """Run git with paths printed as they are (core.quotePath=false); raise GitError if it fails."""
    result = subprocess.run(["git", "-c", "core.quotePath=false", *args], cwd=cwd,
                            capture_output=True, text=True)
    if result.returncode != 0:
        raise GitError(f"`git {args[0]}` failed: {result.stderr.strip()}")
    return result.stdout


def specs(libraries: Sequence[str]) -> list[str]:
    return [f"{library}/*.lean" for library in libraries]


def changed_files(base: str, libraries: Sequence[str] = PRODUCTION_LIBRARIES,
                  cwd: Path = ROOT) -> list[ChangedFile]:
    """The Lean files of `libraries` that `base...HEAD` adds, modifies or renames."""
    common = ["--no-color", "--no-ext-diff", "-M", "--diff-filter=AMR", f"{base}...HEAD", "--"]
    diff = git(["diff", "--unified=0", "--src-prefix=a/", "--dst-prefix=b/", *common,
                *specs(libraries)], cwd)
    statuses = parse_name_status(git(["diff", "--name-status", "-z", *common,
                                      *specs(libraries)], cwd))
    added = parse_diff(diff)
    return [ChangedFile(path, letter, added.get(path, frozenset()), old_path)
            for path, (letter, old_path) in sorted(statuses.items())]


def deleted_files(base: str, libraries: Sequence[str] = PRODUCTION_LIBRARIES,
                  cwd: Path = ROOT) -> list[str]:
    """The Lean files of `libraries` that `base...HEAD` deletes."""
    out = git(["diff", "--name-only", "-z", "-M", "--diff-filter=D", f"{base}...HEAD",
               "--", *specs(libraries)], cwd)
    return [path for path in out.split("\0") if path]


@functools.lru_cache(maxsize=None)
def merge_base(base: str, cwd: Path = ROOT) -> str:
    return git(["merge-base", base, "HEAD"], cwd).strip()


def base_text(base: str, path: str, cwd: Path = ROOT) -> str | None:
    """The text of `path` at the merge base of `base` and HEAD, if it exists there."""
    result = subprocess.run(["git", "show", f"{merge_base(base, cwd)}:{path}"], cwd=cwd,
                            capture_output=True)
    if result.returncode != 0:
        return None
    return result.stdout.decode("utf-8", errors="replace")


@contextlib.contextmanager
def aggregators(files: Sequence[ChangedFile], cwd: Path = ROOT) -> Iterator[list[str]]:
    """Write one aggregator module per library that imports its changed modules.

    Yields the aggregator module names. The files are plain (not `module`), so
    that they can import files of either kind, and are deleted on exit. Raises
    `AggregatorError` if a file of an aggregator's name exists.
    """
    written: list[Path] = []
    names: list[str] = []
    try:
        for library in sorted({file.library for file in files}):
            path = cwd / library / f"{AGGREGATOR}.lean"
            if path.exists():
                raise AggregatorError(
                    f"{path.relative_to(cwd)} exists, so the checks cannot write their "
                    f"aggregator module there; rename that file")
            imports = sorted({file.module for file in files if file.library == library})
            path.write_text("".join(f"import {module}\n" for module in imports))
            written.append(path)
            names.append(f"{library}.{AGGREGATOR}")
        yield names
    finally:
        for path in written:
            path.unlink(missing_ok=True)


def relative(path: str, cwd: Path = ROOT) -> str:
    """A path as Lean prints it (absolute or relative), relative to the repository."""
    return os.path.relpath(Path(cwd, path).resolve(), cwd.resolve()) if path else path


def escape(text: str, property_value: bool = False) -> str:
    text = text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    if property_value:
        text = text.replace(":", "%3A").replace(",", "%2C")
    return text


def annotation(level: str, path: str, line: int, title: str, message: str,
               col: int | None = None) -> str:
    """A GitHub Actions workflow command that annotates `path` at `line` (and 1-based `col`)."""
    fields = [f"file={escape(path, True)}", f"line={line}"]
    if col is not None:
        fields.append(f"col={col}")
    fields.append(f"title={escape(title, True)}")
    return f"::{level} {','.join(fields)}::{escape(message)}"


def in_actions() -> bool:
    return os.environ.get("GITHUB_ACTIONS") == "true"


def write_summary(markdown: str) -> None:
    """Append to the job summary in GitHub Actions; elsewhere, do nothing.

    Like the annotations, the summary is written only when GITHUB_ACTIONS is true, so that a
    run that sets it false (the self-test's runs of the checks) never reaches the job's summary.
    """
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if in_actions() and summary:
        with open(summary, "a", encoding="utf-8") as out:
            out.write(markdown)


def add_common_arguments(parser: argparse.ArgumentParser) -> None:
    """The options that every linter check takes."""
    parser.add_argument("--base", required=True,
                        help="git ref to compare HEAD with (its merge base with HEAD is used)")
    parser.add_argument("--report-only", action="store_true",
                        help="report findings without failing; failures to run still exit 2")


def guarded(main: Callable[[], int]) -> Callable[[], int]:
    """`main`, returning 2 when git cannot read the change, for example for an unknown --base."""
    @functools.wraps(main)
    def run() -> int:
        try:
            return main()
        except GitError as error:
            print(f"Cannot read the change: {error}", file=sys.stderr)
            return 2
    return run


def build(base: str, cwd: Path = ROOT) -> int:
    """Build the changed files of the production libraries through their aggregators."""
    files = changed_files(base, cwd=cwd)
    if not files:
        print("No Lean file of the production libraries is added or modified.")
        return 0
    print(f"Building {len(files)} changed Lean file(s) of the production libraries.")
    try:
        with aggregators(files, cwd) as targets:
            return 0 if subprocess.run(["lake", "build", *targets], cwd=cwd).returncode == 0 else 1
    except AggregatorError as error:
        print(error, file=sys.stderr)
        return 2


@guarded
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    build_parser = commands.add_parser("build", help="build the changed files")
    build_parser.add_argument("--base", required=True, help="git ref to compare HEAD with")
    args = parser.parse_args()
    return build(args.base)


if __name__ == "__main__":
    sys.exit(main())
