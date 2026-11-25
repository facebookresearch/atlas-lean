#!/usr/bin/env python3
"""Regressions for scripts/check_env_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_env_linters.py
"""

from __future__ import annotations

import contextlib
import io
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_env_linters as check
from lean_changes import ROOT, ChangedFile

A = f"{ROOT}/MathlibExt/A.lean"
B = f"{ROOT}/MathlibExt/B.lean"

# What `lake exe runLinter` prints for a module with findings.
OUTPUT = f"""\
Running linter on specified modules: [MathlibExt.LintChanged]
[MathlibExt.LintChanged] --only-modules: 4 local linters lint the 11 declarations of 1 listed modules; the other 11 lint all 56 declarations.
-- Found 4 errors in 24 declarations (plus 32 automatically generated ones) in MathlibExt.LintChanged with 15 linters

/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlame]`. -/
-- MathlibExt.A
{A}:74:1: error: Atlas.probe definition missing documentation string
-- MathlibExt.B
{B}:10:1: error: Atlas.old definition missing documentation string

/- The `unusedArguments` linter reports:
UNUSED ARGUMENTS.
This linter can be disabled with `@[nolint unusedArguments]`. -/
-- MathlibExt.A
{A}:74:1: error: Atlas.probe 1 unused argument:
  argument 2: (m : ℕ)

/- The `simpNF` linter reports:
SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
This linter can be disabled with `@[nolint simpNF]`. -/
#check @Atlas.Thing.mk.injEq /- LINTER FAILED:
maximum recursion depth has been reached -/
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset(range(70, 80))),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({12}))]


def run_main(outputs: list[tuple[int, str]], files=FILES, build_code: int = 0) -> tuple[int, str]:
    @contextlib.contextmanager
    def fake_aggregators(changed):
        yield ["MathlibExt.LintChanged"]

    results = [subprocess.CompletedProcess([], build_code, stdout="", stderr="")]
    results += [subprocess.CompletedProcess([], code, stdout=text, stderr="")
                for code, text in outputs]
    out = io.StringIO()
    with patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", side_effect=results) as run, \
            patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), \
            patch.object(sys, "argv", ["check_env_linters.py", "--base", "HEAD^1"]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
    if files and build_code == 0:
        lint = run.call_args_list[1].args[0]
        assert lint[:5] == ["lake", "exe", "runLinter", "--no-build", lint[4]], lint
        assert lint[4].startswith("--only-modules=") and lint[5] == "MathlibExt.LintChanged", lint
    return code, out.getvalue()


class ParseTests(unittest.TestCase):
    def test_parses_positioned_findings_with_their_linter(self):
        findings = check.parse_run_linter(OUTPUT)
        self.assertEqual([(f.path, f.line, f.linter) for f in findings], [
            ("MathlibExt/A.lean", 74, "docBlame"),
            ("MathlibExt/B.lean", 10, "docBlame"),
            ("MathlibExt/A.lean", 74, "unusedArguments"),
        ])
        self.assertEqual(findings[2].message,
                         "Atlas.probe 1 unused argument:\n  argument 2: (m : ℕ)")


class MainTests(unittest.TestCase):
    def test_keeps_findings_on_declarations_that_start_on_added_lines(self):
        code, out = run_main([(1, OUTPUT)])
        self.assertEqual(code, 1)
        self.assertIn("::warning file=MathlibExt/A.lean,line=74,col=1,title=docBlame::", out)
        self.assertIn("title=unusedArguments::Atlas.probe 1 unused argument:%0A", out)
        self.assertNotIn("B.lean", out)

    def test_passes_when_linting_passes(self):
        code, _ = run_main([(0, "-- Linting passed for MathlibExt.LintChanged.\n")])
        self.assertEqual(code, 0)

    def test_fails_when_the_files_do_not_build(self):
        self.assertEqual(run_main([], build_code=1)[0], 2)

    def test_fails_when_run_linter_does_not_finish(self):
        self.assertEqual(run_main([(1, "uncaught exception: unknown module\n")])[0], 2)


if __name__ == "__main__":
    unittest.main()
