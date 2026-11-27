#!/usr/bin/env python3
"""Regressions for scripts/check_text_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_text_linters.py
"""

from __future__ import annotations

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_text_linters as check
from lean_changes import AggregatorError, ChangedFile, GitError

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

# A new file whose module name holds an apostrophe, which lint-style quotes with backticks;
# with this error alone, lint-style prints no count and exits 1.
APOSTROPHE_OUTPUT = """\
error: module name `MathlibExt.Prime'` contains non-ASCII-alphanumeric character `'`.
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({72})),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({9})),
         ChangedFile("MathlibExt/New_Name.lean", "A", frozenset({1, 2})),
         ChangedFile("MathlibExt/Old_Name.lean", "M", frozenset({4}))]


@contextlib.contextmanager
def job_summary():
    """A job summary of the test's own, so that the fixtures' findings never reach the real one."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "summary.md")
        path.write_text("")
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(path)}):
            yield path


def run_main(output: str, returncode: int, files=FILES, extra=(), aggregator_error=False,
             summary: list[str] | None = None, linted: list | None = None) -> tuple[int, str]:
    """Run main() on fixture output; append the job summary it wrote to `summary`, and the
    files that lint-style was given to `linted`."""
    @contextlib.contextmanager
    def fake_aggregators(changed):
        if aggregator_error:
            raise AggregatorError("MathlibExt/LintChanged.lean exists")
        if linted is not None:
            linted.extend(file.path for file in changed)
        yield ["MathlibExt.LintChanged"]

    result = subprocess.CompletedProcess([], returncode, stdout="", stderr=output)
    out = io.StringIO()
    with job_summary() as summary_path, \
            patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", return_value=result), \
            patch.object(sys, "argv", ["check_text_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
        if summary is not None:
            summary.append(summary_path.read_text())
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

    def test_parses_both_quotings_of_a_module_name_with_an_apostrophe(self):
        paths = {"MathlibExt.Prime'": "MathlibExt/Prime'.lean", "MathlibExt.prime'": "x.lean"}
        errors, reported = check.parse_lint_style(
            APOSTROPHE_OUTPUT + "error: module name 'MathlibExt.prime'' is not in 'UpperCamelCase':"
            " it should be 'MathlibExt.Prime'' instead\n", paths)
        self.assertTrue(reported)
        self.assertEqual([(e.path, e.line, e.module_name) for e in errors],
                         [("MathlibExt/Prime'.lean", 1, True), ("x.lean", 1, True)])
        self.assertEqual(errors[0].message,
                         "Module name contains non-ASCII-alphanumeric character `'`.")

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

    def test_a_module_name_with_an_apostrophe_is_a_finding_not_a_failure(self):
        files = [ChangedFile("MathlibExt/Prime'.lean", "A", frozenset({1, 2, 3}))]
        summary: list[str] = []
        code, out = run_main(APOSTROPHE_OUTPUT, 1, files, extra=["--report-only"],
                             summary=summary)
        self.assertEqual(code, 0)
        self.assertIn("::warning file=MathlibExt/Prime'.lean,line=1,title=lint-style::"
                      "Module name contains non-ASCII-alphanumeric character", out)
        self.assertIn("MathlibExt/Prime'.lean:1", summary[0])
        self.assertEqual(run_main(APOSTROPHE_OUTPUT, 1, files)[0], 1)

    def test_a_name_lean_writes_with_guillemets_is_reported_and_the_rest_is_linted(self):
        # lint-style cannot read `New-Name.lean`, whose module Lean writes `«New-Name»`.
        files = [ChangedFile("MathlibExt/New-Name.lean", "A", frozenset({1, 2})), *FILES]
        linted: list[str] = []
        code, out = run_main(OUTPUT, 1, files=files, linted=linted)
        self.assertEqual(code, 1)
        self.assertNotIn("MathlibExt/New-Name.lean", linted)
        self.assertIn("MathlibExt/A.lean", linted)
        self.assertIn("::error file=MathlibExt/New-Name.lean,line=1,title=lint-style::Module name "
                      "`MathlibExt.«New-Name»` needs «»", out)
        self.assertIn("MathlibExt/A.lean:72:", out)

    def test_a_dotted_file_name_is_reported_and_its_namesake_linted(self):
        # `First.Second.lean` is the module `MathlibExt.«First.Second»`, which lint-style cannot
        # read; `First/Second.lean`, the module `MathlibExt.First.Second`, it reads.
        files = [ChangedFile("MathlibExt/First.Second.lean", "A", frozenset({1})),
                 ChangedFile("MathlibExt/First/Second.lean", "A", frozenset({1}))]
        linted: list[str] = []
        code, out = run_main("", 0, files=files, linted=linted)
        self.assertEqual(code, 1)
        self.assertEqual(linted, ["MathlibExt/First/Second.lean"])
        self.assertIn("MathlibExt/First.Second.lean:1: Module name `MathlibExt.«First.Second»` "
                      "needs «»", out)
        self.assertNotIn("MathlibExt/First/Second.lean:1:", out)

    def test_an_unreadable_base_is_a_failure_to_run(self):
        out = io.StringIO()
        with patch.object(check, "changed_files", side_effect=GitError("no such ref: nope")), \
                patch.object(sys, "argv", ["check_text_linters.py", "--base", "nope"]), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(check.main(), 2)
        self.assertIn("no such ref: nope", out.getvalue())

    def test_passes_without_errors(self):
        self.assertEqual(run_main("", 0)[0], 0)

    def test_fails_when_lint_style_does_not_run(self):
        self.assertEqual(run_main("error: build failed\n", 1, extra=["--report-only"])[0], 2)

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        self.assertEqual(run_main(OUTPUT, 0, aggregator_error=True)[0], 2)


if __name__ == "__main__":
    unittest.main()
