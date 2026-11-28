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
{A}:66:22: warning: This simp argument is unused:
  Nat.mul_comm

Hint: Omit it from the simp argument list.
  simp [Nat.add_comm, N̵a̵t̵.̵m̵u̵l̵_̵c̵o̵m̵m̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-- No environment linters were run for MathlibExt.LintChanged.
"""

# What `lake build` prints when it builds or replays a file with a deprecated name.
BUILD = f"""\
⚠ [1538/1541] Replayed MathlibExt.A
warning: MathlibExt/A.lean:65:50: `Nat.lt_succ` has been deprecated: Use `Nat.lt_succ_iff` instead

Note: `Nat.lt_succ_iff` is protected. References to this constant must include its prefix `Nat` even when inside its namespace.

Hint: Replace the deprecated name:
  Nat.lt_succ_̲i̲f̲f̲
warning: MathlibExt/A.lean:70:4: `Nat.le_step` has been deprecated: Use `Nat.le_succ_of_le` instead
warning: MathlibExt/A.lean:65:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (2671 jobs).
"""

# Every form of deprecation warning, as `lake build` replays them: a deprecated replacement and
# the use of a deprecated name, which only the build log has, and `let_fun` and deprecated
# syntax, which linters log and so `lake lint` prints too (each twice); and a deprecated module,
# whose deprecation is on the second line. One more warning is not a deprecation.
DEPRECATIONS_BUILD = f"""\
⚠ [1538/1541] Replayed MathlibExt.D
warning: MathlibExt/D.lean: imports `Mathlib.Tactic.Ring` from package `mathlib`, which is designed for use with the module system; consider adding `module` to the start of this file
warning: MathlibExt/D.lean:12:2: `D.old` is itself deprecated in favor of `D.new`; consider deprecating `D.older` in favor of `D.new` instead

Note: This warning can be disabled with `set_option linter.deprecated.deprecatedTarget false`

Hint: Deprecate in favor of `D.new` instead:
  o̵l̵d̵n̲e̲w̲
warning: MathlibExt/D.lean:15:29: `D.old` has been deprecated: Use `D.new` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲
warning: MathlibExt/D.lean:17:23: `let_fun` has been deprecated in favor of `have`

Note: This linter can be disabled with `set_option linter.deprecated false`
warning: MathlibExt/D.lean:30:27: syntax 'D.oldSyntax' has been deprecated: write 0

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
warning: MathlibExt/D.lean:3:0: Use the new module instead
'MathlibExt.Old' has been deprecated: please replace this import by

import MathlibExt.New
warning: MathlibExt/D.lean:40:0: unused variable `x`
⚠ [1539/1541] Ran MathlibExt.D:irArts
Build completed successfully (1541 jobs).
"""

DEPRECATIONS_LINT = f"""\
-- Text linter diagnostics in MathlibExt.D:
{ROOT}/MathlibExt/D.lean:17:23: warning: `let_fun` has been deprecated in favor of `have`

Note: This linter can be disabled with `set_option linter.deprecated false`
{ROOT}/MathlibExt/D.lean:17:23: warning: `let_fun` has been deprecated in favor of `have`

Note: This linter can be disabled with `set_option linter.deprecated false`
{ROOT}/MathlibExt/D.lean:30:27: warning: syntax 'D.oldSyntax' has been deprecated: write 0

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
{ROOT}/MathlibExt/D.lean:30:27: warning: syntax 'D.oldSyntax' has been deprecated: write 0

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
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
             build: str = BUILD, build_code: int = 0,
             summary: list[str] | None = None) -> tuple[int, str]:
    """Run main() on fixture output; append the job summary it wrote to `summary`."""
    @contextlib.contextmanager
    def fake_aggregators(changed):
        if aggregator_error:
            raise AggregatorError("MathlibExt/LintChanged.lean exists")
        yield ["MathlibExt.LintChanged"]

    results = [subprocess.CompletedProcess([], build_code, stdout=build, stderr=""),
               subprocess.CompletedProcess([], returncode, stdout=output, stderr="")]
    out = io.StringIO()
    with job_summary() as summary_path, \
            patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", side_effect=results) as run, \
            patch.object(sys, "argv", ["check_syntax_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
        if summary is not None:
            summary.append(summary_path.read_text())
    if files and not aggregator_error:
        assert run.call_args_list[0].args[0] == ["lake", "build", "MathlibExt.LintChanged"]
        if build_code == 0:
            # No linter filter, which would rebuild the files with other options.
            assert run.call_args_list[1].args[0] == [
                "lake", "lint", "--builtin-only", "MathlibExt.LintChanged"], run.call_args_list
    return code, out.getvalue()


class ParseTests(unittest.TestCase):
    def test_parses_each_warning_once_with_its_linter(self):
        warnings = check.parse_lint_output(OUTPUT)
        self.assertEqual([(w.path, w.line, w.col, w.linter) for w in warnings], [
            ("MathlibExt/A.lean", 65, 100, "linter.style.longLine"),
            ("MathlibExt/A.lean", 67, 2, "linter.style.cdot"),
            ("MathlibExt/A.lean", 70, 4, "linter.haveLet"),
            ("MathlibExt/B.lean", 207, 6, "linter.style.show"),
            ("MathlibExt/A.lean", 66, 22, "linter.unusedSimpArgs"),
        ])
        self.assertTrue(warnings[3].message.endswith("instead for these purposes."))
        self.assertNotIn("Note:", warnings[3].message)

    def test_parses_deprecations_from_the_build_log(self):
        warnings = check.parse_deprecations(BUILD)
        self.assertEqual([(w.path, w.line, w.col, w.linter, w.message) for w in warnings], [
            ("MathlibExt/A.lean", 65, 50, "linter.deprecated",
             "`Nat.lt_succ` has been deprecated: Use `Nat.lt_succ_iff` instead"),
            ("MathlibExt/A.lean", 70, 4, "linter.deprecated",
             "`Nat.le_step` has been deprecated: Use `Nat.le_succ_of_le` instead"),
        ])


class DeprecationTests(unittest.TestCase):
    def test_reads_every_form_of_deprecation_as_a_whole_message(self):
        warnings = check.parse_deprecations(DEPRECATIONS_BUILD)
        self.assertEqual([(w.line, w.col, w.linter, w.message.splitlines()[0]) for w in warnings], [
            (12, 2, "linter.deprecated.deprecatedTarget",
             "`D.old` is itself deprecated in favor of `D.new`; consider deprecating `D.older` in "
             "favor of `D.new` instead"),
            (15, 29, "linter.deprecated", "`D.old` has been deprecated: Use `D.new` instead"),
            (17, 23, "linter.deprecated", "`let_fun` has been deprecated in favor of `have`"),
            (30, 27, "linter.deprecated.syntax",
             "syntax 'D.oldSyntax' has been deprecated: write 0"),
            (3, 0, "linter.deprecated", "Use the new module instead"),
        ])
        self.assertNotIn("Hint:", warnings[0].message)
        self.assertIn("import MathlibExt.New", warnings[4].message)

    def test_reports_each_deprecation_once(self):
        files = [ChangedFile("MathlibExt/D.lean", "A", frozenset(range(1, 41)))]
        summary: list[str] = []
        code, out = run_main(DEPRECATIONS_LINT, 1, files=files, build=DEPRECATIONS_BUILD,
                             summary=summary)
        self.assertEqual(code, 1)
        annotations = [line for line in out.splitlines() if line.startswith("::error ")]
        self.assertEqual(sorted(line.split("::")[1] for line in annotations), [
            "error file=MathlibExt/D.lean,line=12,col=3,title=linter.deprecated.deprecatedTarget",
            "error file=MathlibExt/D.lean,line=15,col=30,title=linter.deprecated",
            "error file=MathlibExt/D.lean,line=17,col=24,title=linter.deprecated",
            "error file=MathlibExt/D.lean,line=3,col=1,title=linter.deprecated",
            "error file=MathlibExt/D.lean,line=30,col=28,title=linter.deprecated.syntax",
        ])
        self.assertIn("| `linter.deprecated` | 3 |", summary[0])
        self.assertIn("| `linter.deprecated.syntax` | 1 |", summary[0])
        self.assertIn("| `linter.deprecated.deprecatedTarget` | 1 |", summary[0])

    def test_tool_output_cannot_command_the_runner(self):
        # A deprecation's text is the author's, and can hold a line that reads as a command.
        build = ("warning: MathlibExt/D.lean:15:29: `D.old` has been deprecated: see "
                 "##[error file=MathlibExt/Other.lean;line=1]forged and ##[stop-commands]tok\n"
                 "::error file=MathlibExt/Other.lean,line=1::forged\r::warning::forged\n")
        files = [ChangedFile("MathlibExt/D.lean", "A", frozenset({15}))]
        _, out = run_main("-- No environment linters were run for MathlibExt.LintChanged.\n", 0,
                          files=files, build=build)
        # The check's own annotation is the only command; the runner reads its message as data.
        commands = [line for line in out.splitlines() if line.lstrip().startswith("::")]
        self.assertEqual(len(commands), 1)
        self.assertTrue(commands[0].startswith("::error file=MathlibExt/D.lean,line=15,"))
        self.assertFalse(any("##[" in line for line in out.splitlines() if line not in commands))
        self.assertIn(": :error file=MathlibExt/Other.lean", out)
        self.assertIn("## [stop-commands]tok", out)


class MainTests(unittest.TestCase):
    def test_keeps_only_warnings_on_added_lines(self):
        code, out = run_main(OUTPUT, 1)
        self.assertEqual(code, 1)
        # Lean's column 100 is GitHub's column 101.
        self.assertIn("::error file=MathlibExt/A.lean,line=65,col=101,"
                      "title=linter.style.longLine::", out)
        self.assertIn("::error file=MathlibExt/A.lean,line=65,col=51,title=linter.deprecated::"
                      "`Nat.lt_succ` has been deprecated", out)
        self.assertEqual(out.count("title=linter.style.longLine"), 1)
        self.assertNotIn("A.lean,line=66", out)
        self.assertNotIn("A.lean,line=67", out)
        self.assertNotIn("A.lean,line=70", out)
        self.assertNotIn("B.lean", out)

    def test_reports_default_on_linters(self):
        files = [ChangedFile("MathlibExt/A.lean", "M", frozenset({66}))]
        code, out = run_main(OUTPUT, 1, files)
        self.assertEqual(code, 1)
        self.assertIn("::error file=MathlibExt/A.lean,line=66,col=23,title=linter.unusedSimpArgs::"
                      "This simp argument is unused:%0A  Nat.mul_comm", out)

    def test_fails_when_the_files_do_not_build(self):
        code, _ = run_main(OUTPUT, 0, build="error: MathlibExt/A.lean:3:0: unknown identifier\n",
                           build_code=1, extra=["--report-only"])
        self.assertEqual(code, 2)

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
