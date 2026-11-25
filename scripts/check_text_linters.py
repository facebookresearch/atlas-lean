#!/usr/bin/env python3
"""Report Mathlib's text-based style errors on the lines a change adds.

Mathlib's `lint-style` executable reads the text of Lean files: characters
outside its Unicode allowlist, a space before a semicolon, adaptation notes and
module names. This script runs it on the Lean files that `BASE...HEAD` adds or
modifies (through one temporary aggregator module per library, whose imports
`lint-style` reads) and keeps the errors on lines the change adds, together
with the module-name errors of the files it adds or renames. Code that was
already in a file is not reported. No Lean file needs to be built.

    python3 scripts/check_text_linters.py --base origin/main

Exit 1 if an error is kept, 0 if none, 2 if `lint-style` does not run.
In GitHub Actions each kept error also annotates its line.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_changes import (ROOT, aggregators, annotation, changed_files, in_actions, relative,
                          write_summary)

LINE_ERROR = re.compile(r"^error: (?P<file>\S.*?\.lean):(?P<line>\d+): (?P<message>.*)$")
MODULE_ERROR = re.compile(r"^error: module name ['`](?P<module>[^'`]+)['`] (?P<message>.*)$")
SUMMARY = re.compile(r"^error: found \d+ new style error")


@dataclass(frozen=True)
class StyleError:
    path: str
    line: int
    message: str


def parse_lint_style(text: str, module_paths: dict[str, str],
                     cwd: Path = ROOT) -> tuple[list[StyleError], bool]:
    """The errors that `lint-style` prints, and whether it printed any error at all.

    A module-name error is given line 1 of the module's file, if that file is
    one of `module_paths` (module name to path); other module-name errors are
    dropped.
    """
    errors: list[StyleError] = []
    reported = False
    for line in text.splitlines():
        if SUMMARY.match(line):
            reported = True
        elif match := LINE_ERROR.match(line):
            reported = True
            errors.append(StyleError(relative(match.group("file"), cwd), int(match.group("line")),
                                     match.group("message")))
        elif match := MODULE_ERROR.match(line):
            reported = True
            path = module_paths.get(match.group("module"))
            if path is not None:
                errors.append(StyleError(path, 1, f"Module name {match.group('message')}"))
    return list(dict.fromkeys(errors)), reported


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", required=True,
                        help="git ref to compare HEAD with (its merge base with HEAD is used)")
    args = parser.parse_args()

    files = changed_files(args.base)
    if not files:
        print("No Lean file of the production libraries is added or modified.")
        return 0
    added = {file.path: file.added_lines for file in files}
    # Renaming a file changes its module name, so the name is new code too.
    new_modules = {file.module: file.path for file in files if file.status in "AR"}
    print(f"Checking {len(files)} changed Lean file(s) with Mathlib's lint-style.")
    with aggregators(files) as targets:
        result = subprocess.run(["lake", "exe", "lint-style", *targets], cwd=ROOT,
                                capture_output=True, text=True)
    output = result.stdout + result.stderr
    errors, reported = parse_lint_style(output, new_modules)
    # `lint-style` exits with its error count, so a failure without errors is a failure to run.
    if result.returncode != 0 and not reported:
        print(output, file=sys.stderr)
        print("`lake exe lint-style` did not run.", file=sys.stderr)
        return 2

    kept = [e for e in errors
            if e.line in added.get(e.path, ()) or (e.line == 1 and e.path in new_modules.values())]
    for e in kept:
        if in_actions():
            print(annotation("warning", e.path, e.line, "lint-style", e.message))
        print(f"{e.path}:{e.line}: {e.message}")
    if kept:
        rows = "".join(f"- `{e.path}:{e.line}`: {e.message}\n" for e in kept[:50])
        write_summary(f"### Mathlib text-lint errors on added lines\n\n{rows}\n")
        print(f"{len(kept)} text-lint error(s) on added lines. "
              "`lake exe lint-style --fix <module>` repairs some of them.")
        return 1
    print("No text-lint error on the added lines.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
