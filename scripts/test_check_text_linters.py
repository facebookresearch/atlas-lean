#!/usr/bin/env python3
"""Regressions for scripts/check_text_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_text_linters.py
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

import check_text_linters as check
from lean_changes import ChangedFile

# What `lake exe lint-style` prints (paths relative to the repository).
OUTPUT = """\
warning: nolints file could not be read; treating as empty: scripts/nolints-style.txt
error: found 3 new style error(s)! Try `lake exe lint-style --fix` to apply automatic fixes.
error: MathlibExt/A.lean:72: This line contains a space before a semicolon
error: MathlibExt/A.lean:12: This line contains a unicode character that is not on the allowlist 'ž' (U+017e).
error: MathlibExt/B.lean:3: This line contains a space before a semicolon
error: module name 'MathlibExt.New_Name' is not in 'UpperCamelCase': it should be 'MathlibExt.NewName' instead
error: module name 'MathlibExt.Old_Name' is not in 'UpperCamelCase': it should be 'MathlibExt.OldName' instead
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({72})),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({9})),
         ChangedFile("MathlibExt/New_Name.lean", "A", frozenset({1, 2})),
         ChangedFile("MathlibExt/Old_Name.lean", "M", frozenset({4}))]


def run_main(output: str, returncode: int, files=FILES) -> tuple[int, str]:
    @contextlib.contextmanager
    def fake_aggregators(changed):
        yield ["MathlibExt.LintChanged"]

    result = subprocess.CompletedProcess([], returncode, stdout="", stderr=output)
    out = io.StringIO()
    with patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", return_value=result), \
            patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), \
            patch.object(sys, "argv", ["check_text_linters.py", "--base", "HEAD^1"]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
    return code, out.getvalue()


class ParseTests(unittest.TestCase):
    def test_parses_line_errors_and_module_names_of_new_files(self):
        errors, reported = check.parse_lint_style(
            OUTPUT, {"MathlibExt.New_Name": "MathlibExt/New_Name.lean"})
        self.assertTrue(reported)
        self.assertEqual([(e.path, e.line) for e in errors], [
            ("MathlibExt/A.lean", 72), ("MathlibExt/A.lean", 12), ("MathlibExt/B.lean", 3),
            ("MathlibExt/New_Name.lean", 1)])
        self.assertTrue(errors[3].message.startswith("Module name is not in 'UpperCamelCase'"))

    def test_nothing_reported(self):
        self.assertEqual(check.parse_lint_style("", {}), ([], False))


class MainTests(unittest.TestCase):
    def test_keeps_errors_on_added_lines_and_names_of_added_files(self):
        code, out = run_main(OUTPUT, 5)
        self.assertEqual(code, 1)
        self.assertIn("::warning file=MathlibExt/A.lean,line=72,title=lint-style::", out)
        self.assertIn("::warning file=MathlibExt/New_Name.lean,line=1,title=lint-style::", out)
        self.assertNotIn("A.lean,line=12", out)
        self.assertNotIn("B.lean", out)
        self.assertNotIn("Old_Name", out)

    def test_passes_without_errors(self):
        self.assertEqual(run_main("", 0)[0], 0)

    def test_fails_when_lint_style_does_not_run(self):
        self.assertEqual(run_main("error: build failed\n", 1)[0], 2)


if __name__ == "__main__":
    unittest.main()
