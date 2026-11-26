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
from lean_changes import AggregatorError, ChangedFile

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

# A renamed file whose first line, which the change does not add, has two content errors.
RENAMED_OUTPUT = """\
error: found 2 new style error(s)! Try `lake exe lint-style --fix` to apply automatic fixes.
error: MathlibExt/Moved.lean:1: This line contains a windows line ending
error: MathlibExt/Moved.lean:1: This line contains a unicode character that is not on the allowlist 'ž' (U+017e).
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({72})),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({9})),
         ChangedFile("MathlibExt/New_Name.lean", "A", frozenset({1, 2})),
         ChangedFile("MathlibExt/Old_Name.lean", "M", frozenset({4}))]


def run_main(output: str, returncode: int, files=FILES, extra=(), aggregator_error=False
             ) -> tuple[int, str]:
    @contextlib.contextmanager
    def fake_aggregators(changed):
        if aggregator_error:
            raise AggregatorError("MathlibExt/LintChanged.lean exists")
        yield ["MathlibExt.LintChanged"]

    result = subprocess.CompletedProcess([], returncode, stdout="", stderr=output)
    out = io.StringIO()
    with patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", return_value=result), \
            patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), \
            patch.object(sys, "argv", ["check_text_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
    return code, out.getvalue()


class ParseTests(unittest.TestCase):
    def test_parses_line_errors_and_module_names_of_new_files(self):
        errors, reported = check.parse_lint_style(
            OUTPUT, {"MathlibExt.New_Name": "MathlibExt/New_Name.lean"})
        self.assertTrue(reported)
        self.assertEqual([(e.path, e.line, e.module_name) for e in errors], [
            ("MathlibExt/A.lean", 72, False), ("MathlibExt/A.lean", 12, False),
            ("MathlibExt/B.lean", 3, False), ("MathlibExt/New_Name.lean", 1, True)])
        self.assertTrue(errors[3].message.startswith("Module name is not in 'UpperCamelCase'"))

    def test_nothing_reported(self):
        self.assertEqual(check.parse_lint_style("", {}), ([], False))


class MainTests(unittest.TestCase):
    def test_keeps_errors_on_added_lines_and_names_of_added_files(self):
        code, out = run_main(OUTPUT, 5)
        self.assertEqual(code, 1)
        self.assertIn("::error file=MathlibExt/A.lean,line=72,title=lint-style::", out)
        self.assertIn("::error file=MathlibExt/New_Name.lean,line=1,title=lint-style::Module name",
                      out)
        self.assertNotIn("A.lean,line=12", out)
        self.assertNotIn("B.lean", out)
        self.assertNotIn("Old_Name", out)

    def test_a_renamed_file_reports_its_name_but_not_its_old_first_line(self):
        files = [ChangedFile("MathlibExt/Moved.lean", "R", frozenset(), "MathlibExt/Old.lean")]
        code, out = run_main(RENAMED_OUTPUT, 2, files)
        self.assertEqual(code, 0)
        self.assertNotIn("::", out)

    def test_report_only_annotates_and_passes(self):
        code, out = run_main(OUTPUT, 5, extra=["--report-only"])
        self.assertEqual(code, 0)
        self.assertIn("::warning file=MathlibExt/A.lean,line=72,title=lint-style::", out)

    def test_passes_without_errors(self):
        self.assertEqual(run_main("", 0)[0], 0)

    def test_fails_when_lint_style_does_not_run(self):
        self.assertEqual(run_main("error: build failed\n", 1, extra=["--report-only"])[0], 2)

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        self.assertEqual(run_main(OUTPUT, 0, aggregator_error=True)[0], 2)


if __name__ == "__main__":
    unittest.main()
