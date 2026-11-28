#!/usr/bin/env python3
"""Regressions for scripts/check_syntax_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_syntax_linters.py
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

import check_syntax_linters as check
from lean_changes import ROOT, AggregatorError, ChangedFile, GitError

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
{A}:70:4: warning: 'this : Fintype ι' is a Type and not a Prop. Consider using 'let' instead of 'have'.

Note: This linter can be disabled with `set_option linter.haveLet 0`
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


@contextlib.contextmanager
def job_summary():
    """A job summary of the test's own, so that the fixtures' findings never reach the real one."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "summary.md")
        path.write_text("")
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(path)}):
            yield path


def run_main(output: str, returncode: int, files=FILES, extra=(), aggregator_error=False,
             summary: list[str] | None = None) -> tuple[int, str]:
    """Run main() on fixture output; append the job summary it wrote to `summary`."""
    @contextlib.contextmanager
    def fake_aggregators(changed):
        if aggregator_error:
            raise AggregatorError("MathlibExt/LintChanged.lean exists")
        yield ["MathlibExt.LintChanged"]

    result = subprocess.CompletedProcess([], returncode, stdout=output, stderr="")
    out = io.StringIO()
    with job_summary() as summary_path, \
            patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", return_value=result) as run, \
            patch.object(sys, "argv", ["check_syntax_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
        if summary is not None:
            summary.append(summary_path.read_text())
    if files and not aggregator_error:
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
            ("MathlibExt/A.lean", 70, 4, "linter.haveLet"),
            ("MathlibExt/B.lean", 207, 6, "linter.style.show"),
        ])
        self.assertTrue(warnings[3].message.endswith("instead for these purposes."))
        self.assertNotIn("Note:", warnings[3].message)


class MainTests(unittest.TestCase):
    def test_keeps_only_warnings_on_added_lines(self):
        code, out = run_main(OUTPUT, 1)
        self.assertEqual(code, 1)
        # Lean's column 100 is GitHub's column 101.
        self.assertIn("::error file=MathlibExt/A.lean,line=65,col=101,"
                      "title=linter.style.longLine::", out)
        self.assertNotIn("A.lean,line=67", out)
        self.assertNotIn("B.lean", out)

    def test_report_only_annotates_and_passes(self):
        summary: list[str] = []
        code, out = run_main(OUTPUT, 1, extra=["--report-only"], summary=summary)
        self.assertEqual(code, 0)
        self.assertIn("| `linter.style.longLine` | 1 |", summary[0])
        self.assertIn("::warning file=MathlibExt/A.lean,line=65,col=101,", out)

    def test_passes_when_no_warning_is_on_an_added_line(self):
        files = [ChangedFile("MathlibExt/A.lean", "M", frozenset({1})),
                 ChangedFile("MathlibExt/B.lean", "M", frozenset({2}))]
        summary: list[str] = []
        code, out = run_main(OUTPUT, 1, files, summary=summary)
        self.assertEqual(code, 0)
        self.assertNotIn("::", out)
        self.assertEqual(summary, [""])

    def test_an_unreadable_base_is_a_failure_to_run(self):
        out = io.StringIO()
        with patch.object(check, "changed_files", side_effect=GitError("no such ref: nope")), \
                patch.object(sys, "argv", ["check_syntax_linters.py", "--base", "nope"]), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(check.main(), 2)
        self.assertIn("no such ref: nope", out.getvalue())

    def test_fails_when_lake_lint_does_not_reach_the_lint(self):
        code, _ = run_main("error: MathlibExt/A.lean:3:0: unknown identifier\nerror: build failed\n",
                           1, extra=["--report-only"])
        self.assertEqual(code, 2)

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        code, _ = run_main(OUTPUT, 0, aggregator_error=True)
        self.assertEqual(code, 2)

    def test_nothing_to_check(self):
        code, out = run_main("", 0, files=[])
        self.assertEqual(code, 0)
        self.assertIn("No Lean file", out)


if __name__ == "__main__":
    unittest.main()
