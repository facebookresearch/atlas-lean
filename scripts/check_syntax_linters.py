#!/usr/bin/env python3
"""Report the linter and deprecation warnings that a change adds.

Every build already runs Lean's, Batteries' and Mathlib's default-on linters,
and the production libraries also run `linter.mathlibStandardSet`, which
lakefile.toml turns on. Lake keeps their warnings in the `.olean` files. This
script builds the Lean files that `BASE...HEAD` adds or modifies (through one
temporary aggregator module per library), reads the warnings of every linter
with `lake lint`, and keeps those on lines the change adds. Lean does not keep
deprecation warnings with the linters', so the script also reads them from the
log that Lake replays when it builds the files. Code that was already in a file
is not reported.

    python3 scripts/check_syntax_linters.py --base origin/main [--report-only]

Exit 1 if a warning is kept (0 with --report-only), 0 if none, 2 if the files do
not build or the lint does not run. In GitHub Actions each kept warning also
annotates its line and the job summary counts them.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_changes import (ROOT, AggregatorError, add_common_arguments, aggregators, annotation,
                          changed_files, guarded, in_actions, relative, write_summary)

ENTRY = re.compile(r"^(?P<file>\S.*?\.lean):(?P<line>\d+):(?P<col>\d+): "
                   r"(?P<severity>warning|error|information): (?P<text>.*)$")
# A Bool linter prints `false`, a Nat one (`linter.haveLet`) `0`.
NOTE = re.compile(r"^Note: This linter can be disabled with `set_option (?P<linter>\S+) \S+`$")
# `lake lint` prints one of these for each target that it lints.
LINTED = re.compile(r"^-- (?:No environment linters were run|Environment linting passed) for ")
# How `lake build` prints a message, when it builds a file or replays the file's log.
BUILD_ENTRY = re.compile(r"^(?P<severity>warning|error|info): (?P<file>\S.*?\.lean):(?P<line>\d+):"
                         r"(?P<col>\d+): (?P<text>.*)$")
DEPRECATION = "linter.deprecated"


@dataclass(frozen=True)
class LintWarning:
    """A warning at a 1-based line and the 0-based column that Lean prints."""

    path: str
    line: int
    col: int
    linter: str
    message: str


def parse_lint_output(text: str, cwd: Path = ROOT) -> list[LintWarning]:
    """The linter warnings that `lake lint --builtin-only` prints, without repeats."""
    warnings: list[LintWarning] = []
    current: tuple[re.Match[str], list[str]] | None = None

    def finish() -> None:
        if current is None:
            return
        match, body = current
        linter = ""
        lines = []
        for line in body:
            note = NOTE.match(line)
            if note:
                linter = note.group("linter")
            else:
                lines.append(line)
        message = "\n".join([match.group("text"), *lines]).strip()
        warnings.append(LintWarning(relative(match.group("file"), cwd), int(match.group("line")),
                                    int(match.group("col")), linter, message))

    for line in text.splitlines():
        match = ENTRY.match(line)
        if match:
            finish()
            current = (match, [])
        elif line.startswith("-- "):
            finish()
            current = None
        elif current is not None:
            current[1].append(line)
    finish()
    return list(dict.fromkeys(warnings))


def parse_deprecations(text: str, cwd: Path = ROOT) -> list[LintWarning]:
    """The deprecation warnings in `lake build` output, without repeats.

    Only the first line of each is kept: it names the deprecated declaration and,
    when there is one, its replacement.
    """
    warnings = []
    for line in text.splitlines():
        match = BUILD_ENTRY.match(line)
        if match and match.group("severity") == "warning" and \
                " has been deprecated" in match.group("text"):
            warnings.append(LintWarning(relative(match.group("file"), cwd), int(match.group("line")),
                                        int(match.group("col")), DEPRECATION,
                                        match.group("text").strip()))
    return list(dict.fromkeys(warnings))


@guarded
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    add_common_arguments(parser)
    args = parser.parse_args()

    files = changed_files(args.base)
    if not files:
        print("No Lean file of the production libraries is added or modified.")
        return 0
    added = {file.path: file.added_lines for file in files}
    print(f"Checking {len(files)} changed Lean file(s) for linter and deprecation warnings.")
    try:
        with aggregators(files) as targets:
            # Lake replays the log of a file it has built already, deprecations included.
            build = subprocess.run(["lake", "build", *targets], cwd=ROOT, capture_output=True,
                                   text=True)
            if build.returncode != 0:
                print(build.stdout + build.stderr, file=sys.stderr)
                print("The changed files do not build.", file=sys.stderr)
                return 2
            # No `--linters` or `--lint-only`: either would rebuild the files with other options.
            result = subprocess.run(["lake", "lint", "--builtin-only", *targets], cwd=ROOT,
                                    capture_output=True, text=True)
    except AggregatorError as error:
        print(error, file=sys.stderr)
        return 2
    output = result.stdout + result.stderr
    if result.returncode not in (0, 1) or len(
            [line for line in output.splitlines() if LINTED.match(line)]) < len(targets):
        print(output, file=sys.stderr)
        print("`lake lint` did not run.", file=sys.stderr)
        return 2

    warnings = parse_lint_output(output) + parse_deprecations(build.stdout + build.stderr)
    kept = [w for w in warnings if w.line in added.get(w.path, ())]
    level = "warning" if args.report_only else "error"
    for w in kept:
        if in_actions():
            # GitHub counts columns from 1, Lean from 0.
            print(annotation(level, w.path, w.line, w.linter, w.message, w.col + 1))
        print(f"{w.path}:{w.line}:{w.col}: {w.linter}: {w.message}")
    counts = Counter(w.linter for w in kept)
    if kept:
        rows = "".join(f"| `{linter or 'unnamed'}` | {count} |\n"
                       for linter, count in counts.most_common())
        write_summary(f"### Linter and deprecation warnings on added lines\n\n"
                      f"| Linter | Warnings |\n|---|---:|\n{rows}\n")
        print(f"{len(kept)} warning(s) on added lines. Fix them, or where a linter's warning is "
              "wrong, turn it off for that declaration with `set_option <linter> false in`.")
        return 0 if args.report_only else 1
    print("No linter or deprecation warning on the added lines.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
