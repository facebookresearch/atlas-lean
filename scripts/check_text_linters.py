#!/usr/bin/env python3
"""Report Mathlib's text-based style errors on the lines a change adds.

Mathlib's `lint-style` executable reads the text of Lean files: characters
outside its Unicode allowlist, a space before a semicolon, adaptation notes and
module names. This script runs it on the Lean files that `BASE...HEAD` adds or
modifies (through one temporary aggregator module per library, whose imports
`lint-style` reads) and keeps the errors on lines the change adds, together
with the module-name errors of the files it adds or renames. Code that was
already in a file is not reported. No Lean file needs to be built.

    python3 scripts/check_text_linters.py --base origin/main [--report-only]

Exit 1 if an error is kept (0 with --report-only), 0 if none, 2 if `lint-style`
does not run. In GitHub Actions each kept error also annotates its line.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_changes import (ROOT, AggregatorError, add_common_arguments, aggregators, annotation,
                          changed_files, guarded, in_actions, inert, lean_unescaped, printable,
                          relative, write_summary)

LINE_ERROR = re.compile(r"^error: (?P<file>\S.*?\.lean):(?P<line>\d+): (?P<message>.*)$")
# Module-name errors quote the name in one of two ways, and a name can hold an apostrophe:
# "module name 'M' is not in 'UpperCamelCase': ..." and "module name `M` contains ...".
MODULE_ERROR = re.compile(r"^error: module name (?:'(?P<quoted>.+?)' (?=is not in )|"
                          r"`(?P<ticked>[^`]+)` )(?P<message>.*)$")
# Any other module-name error still shows that lint-style ran.
OTHER_MODULE_ERROR = re.compile(r"^error: module name ")
SUMMARY = re.compile(r"^error: found \d+ new style error")


@dataclass(frozen=True)
class StyleError:
    """An error on a line of a file, or (`module_name`) about the name of the file's module."""

    path: str
    line: int
    message: str
    module_name: bool = False


def parse_lint_style(text: str, module_paths: dict[str, str],
                     cwd: Path = ROOT) -> tuple[list[StyleError], bool]:
    """The errors that `lint-style` prints, and whether it printed any error at all.

    A module-name error is placed on line 1 of the module's file, if that file is
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
            path = module_paths.get(
                lean_unescaped(match.group("quoted") or match.group("ticked")))
            if path is not None:
                errors.append(StyleError(path, 1, f"Module name {match.group('message')}",
                                         module_name=True))
        elif OTHER_MODULE_ERROR.match(line):
            reported = True
            print(f"Not understood: {inert(line)}", file=sys.stderr)
    return list(dict.fromkeys(errors)), reported


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
    # Renaming a file changes its module name, so the name is new code too.
    new_modules = {file.module: file.path for file in files if file.status in "AR"}
    # lint-style finds a module's file from its name as Lean prints it, so it cannot read a file
    # whose name Lean writes with «», such as `New-Name.lean`; that name is reported instead.
    unreadable = [file for file in files
                  if file.lean_module is not None and file.lean_module != file.module]
    errors = [StyleError(file.path, 1, f"Module name `{file.lean_module}` needs «», which "
                         f"Mathlib's lint-style cannot read; name the file in UpperCamelCase",
                         module_name=True)
              for file in unreadable]
    for file in unreadable:
        if file.status not in "AR":
            print(inert(f"{printable(file.path)}: lint-style cannot read this file, so its added "
                        f"lines are not checked."), file=sys.stderr)
    files = [file for file in files if file not in unreadable]
    print(f"Checking {len(files)} changed Lean file(s) with Mathlib's lint-style.")
    try:
        with aggregators(files) as targets:
            result = None
            if targets:
                result = subprocess.run(["lake", "exe", "lint-style", *targets], cwd=ROOT,
                                        capture_output=True, text=True)
    except AggregatorError as error:
        print(inert(str(error)), file=sys.stderr)
        return 2
    if result is not None:
        output = result.stdout + result.stderr
        found, reported = parse_lint_style(output, new_modules)
        errors += found
        # `lint-style` exits with its error count, so a failure without errors is a failure to
        # run.
        if result.returncode != 0 and not reported:
            print(inert(output), file=sys.stderr)
            print("`lake exe lint-style` did not run.", file=sys.stderr)
            return 2

    # A line error is new when its line is added; a module-name error when the
    # change adds or renames the file. Line 1 of a renamed file is not added.
    kept = [e for e in errors
            if (e.module_name and e.path in new_modules.values())
            or (not e.module_name and e.line in added.get(e.path, ()))]
    level = "warning" if args.report_only else "error"
    for e in kept:
        if in_actions():
            print(annotation(level, e.path, e.line, "lint-style", e.message))
        print(inert(f"{e.path}:{e.line}: {e.message}"))
    if kept:
        rows = "".join(f"- `{e.path}:{e.line}`: {e.message}\n" for e in kept[:50])
        write_summary(f"### Mathlib text-lint errors on added lines\n\n{rows}\n")
        print(f"{len(kept)} text-lint error(s) on added lines. "
              "`lake exe lint-style --fix <module>` repairs some of them.")
        return 0 if args.report_only else 1
    print("No text-lint error on the added lines.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
