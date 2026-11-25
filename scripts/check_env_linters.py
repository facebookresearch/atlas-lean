#!/usr/bin/env python3
"""Report Mathlib's environment-linter findings on the declarations a change adds.

The environment linters of Batteries' `#lint`, with the ones Mathlib adds
(`docBlame`, `simpNF`, `unusedArguments`, `defsWithUnderscore`, ...), check
declarations after they are built. This script builds the Lean files that
`BASE...HEAD` adds or modifies (through one temporary aggregator module per
library), runs `lake exe runLinter` on each aggregator, and keeps the findings
on declarations that start on a line the change adds. Declarations that were
already there are not reported. As in Mathlib, `runLinter` sees what modules
export, so in a `module` file it lints the public declarations only.

    python3 scripts/check_env_linters.py --base origin/main

Exit 1 if a finding is kept, 0 if none, 2 if the files do not build or the
linter does not run. In GitHub Actions each kept finding also annotates its line.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_changes import (ROOT, aggregators, annotation, changed_files, in_actions, relative,
                          write_summary)

ENTRY = re.compile(r"^(?P<file>\S.*?\.lean):(?P<line>\d+):(?P<col>\d+): error: (?P<text>.*)$")
HEADER = re.compile(r"^/- The `(?P<linter>[^`]+)` linter reports:")
# `runLinter` prints one of these when it has linted its module.
FINISHED = re.compile(r"^-- (?:Found \d+ errors? in|Linting passed for) ")


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    col: int
    linter: str
    message: str


def parse_run_linter(text: str, cwd: Path = ROOT) -> list[Finding]:
    """The findings with a source position that `runLinter` prints, by linter."""
    findings: list[Finding] = []
    linter = "environment linter"
    current: tuple[re.Match[str], list[str]] | None = None

    def finish() -> None:
        if current is not None:
            match, body = current
            message = "\n".join([match.group("text"), *body]).strip()
            findings.append(Finding(relative(match.group("file"), cwd), int(match.group("line")),
                                    int(match.group("col")), linter, message))

    for line in text.splitlines():
        if header := HEADER.match(line):
            finish()
            current = None
            linter = header.group("linter")
        elif match := ENTRY.match(line):
            finish()
            current = (match, [])
        elif not line.strip() or line.startswith(("-- ", "#check ", "/-")):
            finish()
            current = None
        elif current is not None:
            current[1].append(line)
    finish()
    return list(dict.fromkeys(findings))


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
    print(f"Checking the declarations of {len(files)} changed Lean file(s) with runLinter.")
    outputs = []
    with aggregators(files) as targets, tempfile.TemporaryDirectory() as tmp:
        build = subprocess.run(["lake", "build", *targets], cwd=ROOT, capture_output=True,
                               text=True)
        if build.returncode != 0:
            print(build.stdout + build.stderr, file=sys.stderr)
            print("The changed files do not build.", file=sys.stderr)
            return 2
        for target in targets:
            library = target.split(".", 1)[0]
            # Local linters such as docBlame then lint only the changed modules.
            only = Path(tmp, f"{library}.txt")
            only.write_text("".join(f"{file.module}\n" for file in files
                                    if file.library == library))
            result = subprocess.run(
                ["lake", "exe", "runLinter", "--no-build", f"--only-modules={only}", target],
                cwd=ROOT, capture_output=True, text=True)
            output = result.stdout + result.stderr
            if result.returncode not in (0, 1) or not any(
                    FINISHED.match(line) for line in output.splitlines()):
                print(output, file=sys.stderr)
                print(f"runLinter did not run on {target}.", file=sys.stderr)
                return 2
            outputs.append(output)

    kept = [f for output in outputs for f in parse_run_linter(output)
            if f.line in added.get(f.path, ())]
    kept = list(dict.fromkeys(kept))
    for f in kept:
        if in_actions():
            print(annotation("warning", f.path, f.line, f.linter, f.message, f.col))
        print(f"{f.path}:{f.line}:{f.col}: {f.linter}: {f.message}")
    if kept:
        counts = Counter(f.linter for f in kept)
        rows = "".join(f"| `{linter}` | {count} |\n" for linter, count in counts.most_common())
        write_summary(f"### Environment-linter findings on added declarations\n\n"
                      f"| Linter | Findings |\n|---|---:|\n{rows}\n")
        print(f"{len(kept)} finding(s) on added declarations. Fix them, or where a finding is "
              "wrong, mark the declaration `@[nolint <linter>]`.")
        return 1
    print("No environment-linter finding on the added declarations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
