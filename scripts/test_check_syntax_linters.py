#!/usr/bin/env python3
"""Regressions for scripts/check_syntax_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_syntax_linters.py
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

import check_syntax_linters as check
from lean_changes import ROOT, ChangedFile

A = f"{ROOT}/MathlibExt/A.lean"
B = f"{ROOT}/MathlibExt/B.lean"

# What `lake lint --builtin-only` prints; Lake lists some warnings twice.
OUTPUT = f"""\
✔ [5490/5491] Built MathlibExt.LintChanged (1.6s)
-- Text linter diagnostics in MathlibExt.A:
{A}:65:100: warning: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
{A}:67:2: warning: This central dot `·` is isolated; please merge it with the next line.

Note: This linter can be disabled with `set_option linter.style.cdot false`
-- Text linter diagnostics in MathlibExt.B:
{B}:207:6: warning: The `show` tactic should only be used to indicate intermediate goal states for readability.
However, this tactic invocation changed the goal. Please use `change` instead for these purposes.

Note: This linter can be disabled with `set_option linter.style.show false`
{B}:207:6: warning: The `show` tactic should only be used to indicate intermediate goal states for readability.
However, this tactic invocation changed the goal. Please use `change` instead for these purposes.

Note: This linter can be disabled with `set_option linter.style.show false`
-- No environment linters were run for MathlibExt.LintChanged.
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({65})),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({205}))]


def run_main(output: str, returncode: int, files=FILES) -> tuple[int, str]:
    @contextlib.contextmanager
    def fake_aggregators(changed):
        yield ["MathlibExt.LintChanged"]

    result = subprocess.CompletedProcess([], returncode, stdout=output, stderr="")
    out = io.StringIO()
    with patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", return_value=result) as run, \
            patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), \
            patch.object(sys, "argv", ["check_syntax_linters.py", "--base", "HEAD^1"]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
    if files:
        args = run.call_args.args[0]
        assert args[:4] == ["lake", "lint", "--builtin-only",
                            "--lint-only=linter.mathlibStandardSet"], args
    return code, out.getvalue()


class ParseTests(unittest.TestCase):
    def test_parses_each_warning_once_with_its_linter(self):
        warnings = check.parse_lint_output(OUTPUT)
        self.assertEqual([(w.path, w.line, w.col, w.linter) for w in warnings], [
            ("MathlibExt/A.lean", 65, 100, "linter.style.longLine"),
            ("MathlibExt/A.lean", 67, 2, "linter.style.cdot"),
            ("MathlibExt/B.lean", 207, 6, "linter.style.show"),
        ])
        self.assertTrue(warnings[2].message.endswith("instead for these purposes."))
        self.assertNotIn("Note:", warnings[2].message)


class MainTests(unittest.TestCase):
    def test_keeps_only_warnings_on_added_lines(self):
        code, out = run_main(OUTPUT, 1)
        self.assertEqual(code, 1)
        self.assertIn("::warning file=MathlibExt/A.lean,line=65,col=100,"
                      "title=linter.style.longLine::", out)
        self.assertNotIn("A.lean,line=67", out)
        self.assertNotIn("B.lean", out)

    def test_passes_when_no_warning_is_on_an_added_line(self):
        files = [ChangedFile("MathlibExt/A.lean", "M", frozenset({1})),
                 ChangedFile("MathlibExt/B.lean", "M", frozenset({2}))]
        code, out = run_main(OUTPUT, 1, files)
        self.assertEqual(code, 0)
        self.assertNotIn("::warning", out)

    def test_fails_when_lake_lint_does_not_reach_the_lint(self):
        code, _ = run_main("error: MathlibExt/A.lean:3:0: unknown identifier\nerror: build failed\n",
                           1)
        self.assertEqual(code, 2)

    def test_nothing_to_check(self):
        code, out = run_main("", 0, files=[])
        self.assertEqual(code, 0)
        self.assertIn("No Lean file", out)


if __name__ == "__main__":
    unittest.main()
