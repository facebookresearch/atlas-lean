#!/usr/bin/env python3
"""Report Mathlib's standard linter warnings on the lines a change adds.

lakefile.toml builds the production libraries with `linter.mathlibStandardSet`,
so every build already runs these linters, and Lake keeps their warnings in the
`.olean` files. This script builds the Lean files that `BASE...HEAD` adds or
modifies (through one temporary aggregator module per library), reads their
warnings with `lake lint`, and keeps the warnings on lines the change adds.
Code that was already in a file is not reported.

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
                          changed_files, guarded, in_actions, inert, relative, write_summary)

LINTER_SET = "linter.mathlibStandardSet"

ENTRY = re.compile(r"^(?P<file>\S.*?\.lean):(?P<line>\d+):(?P<col>\d+): "
                   r"(?P<severity>warning|error|information): (?P<text>.*)$")
# A Bool linter prints `false`, a Nat one (`linter.haveLet`) `0`.
NOTE = re.compile(r"^Note: This linter can be disabled with `set_option (?P<linter>\S+) \S+`$")
# `lake lint` prints one of these for each target that it lints.
LINTED = re.compile(r"^-- (?:No environment linters were run|Environment linting passed) for ")


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
    print(f"Checking {len(files)} changed Lean file(s) for {LINTER_SET} warnings.")
    try:
        with aggregators(files) as targets:
            if not targets:
                return 0
            result = subprocess.run(
                ["lake", "lint", "--builtin-only", f"--lint-only={LINTER_SET}", *targets],
                cwd=ROOT, capture_output=True, text=True)
    except AggregatorError as error:
        print(error, file=sys.stderr)
        return 2
    output = result.stdout + result.stderr
    if result.returncode not in (0, 1) or len(
            [line for line in output.splitlines() if LINTED.match(line)]) < len(targets):
        print(inert(output), file=sys.stderr)
        print("The changed files did not build, or `lake lint` did not run.", file=sys.stderr)
        return 2

    kept = [w for w in parse_lint_output(output) if w.line in added.get(w.path, ())]
    level = "warning" if args.report_only else "error"
    for w in kept:
        if in_actions():
            # GitHub counts columns from 1, Lean from 0.
            print(annotation(level, w.path, w.line, w.linter, w.message, w.col + 1))
        print(inert(f"{w.path}:{w.line}:{w.col}: {w.linter}: {w.message}"))
    counts = Counter(w.linter for w in kept)
    if kept:
        rows = "".join(f"| `{linter}` | {count} |\n" for linter, count in counts.most_common())
        write_summary(f"### Mathlib linter warnings on added lines\n\n| Linter | Warnings |\n"
                      f"|---|---:|\n{rows}\n")
        print(f"{len(kept)} warning(s) on added lines. Fix them, or where a warning is wrong, "
              f"turn its linter off for that declaration with `set_option <linter> false in`.")
        return 0 if args.report_only else 1
    print("No Mathlib linter warning on the added lines.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
