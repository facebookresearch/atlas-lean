#!/usr/bin/env python3
"""Regressions for scripts/check_unused_imports.py; never invokes Lean, Lake or agitate.

Run with: python3 -m unittest discover -s scripts -p test_check_unused_imports.py
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

import check_unused_imports as check
from lean_changes import ROOT, ChangedFile, GitError

A = f"{ROOT}/MathlibExt/A.lean"
B = f"{ROOT}/MathlibExt/B.lean"
D = f"{ROOT}/MathlibExt/D.lean"

SOURCES = {
    "MathlibExt/A.lean": """\
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
/- a nested comment -/
-/

module -- shake: keep-downstream

public import Mathlib.Order.Basic
import Mathlib.Tactic.Ring  -- an unused import
import Mathlib.Tactic.Linarith
public meta import MathlibExt.C
import all MathlibExt.E

/-! # A module docstring -/

@[expose] public section

theorem t : True := trivial
""",
    "MathlibExt/B.lean": """\
import Mathlib.Order.Basic
import MathlibExt.Marked.Iso

/-! Not a module. -/

open CategoryTheory
""",
}

# What `agitate --gh-style` prints: for A, two removals of which the change adds
# line 9, and an addition; for D, which the change does not touch, an addition.
MODULE_OUTPUT = f"""\
{D}:
{D}:7:1: warning: add #[public import Mathlib.Tactic.TypeStar] instead
  add #[public import Mathlib.Tactic.TypeStar]
{A}:
  remove #[import Mathlib.Tactic.Ring, import Mathlib.Tactic.Linarith]
{A}:9:1: warning: unused import (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)
{A}:10:1: warning: unused import (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)
{A}:12:1: warning: add #[import Mathlib.Tactic.Linarith.Frontend] instead
  add #[import Mathlib.Tactic.Linarith.Frontend]
"""

NONMODULE_OUTPUT = f"""\
{B}:
  remove #[import MathlibExt.Marked.Iso]
{B}:2:1: warning: unused import (use `lake shake --fix` to fix this, or `lake shake --update` to ignore)
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({9, 17})),
         ChangedFile("MathlibExt/B.lean", "A", frozenset(range(1, 7)))]


@contextlib.contextmanager
def agitate_build(toolchain: str | None = None):
    """A directory shaped like a built agitate checkout."""
    with tempfile.TemporaryDirectory() as tmp:
        bin_dir = Path(tmp, ".lake", "build", "bin")
        bin_dir.mkdir(parents=True)
        for tool in ("agitate", "agitate-nonmodule"):
            (bin_dir / tool).write_text("")
        ours = (ROOT / "lean-toolchain").read_text()
        Path(tmp, "lean-toolchain").write_text(toolchain if toolchain is not None else ours)
        yield tmp


@contextlib.contextmanager
def job_summary():
    """A job summary of the test's own, so that the fixtures' findings never reach the real one."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "summary.md")
        path.write_text("")
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(path),
                                       "AGITATE_DIR": ""}):
            yield path


def run_main(results, files=FILES, extra=(), toolchain=None, agitate_dir=True,
             summary: list[str] | None = None):
    """Run main() with `results` as the agitate runs, in order; return code, output, calls.

    The job summary that main() writes is appended to `summary`."""
    if not isinstance(results, list):
        results = [results]
    out = io.StringIO()
    with agitate_build(toolchain) as tmp, job_summary() as summary_path, \
            patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "read_source", side_effect=SOURCES.__getitem__), \
            patch.object(check.subprocess, "run", side_effect=results) as run, \
            patch.object(sys, "argv", ["check_unused_imports.py", "--base", "HEAD^1",
                                       *(["--agitate-dir", tmp] if agitate_dir else []),
                                       *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
        code = check.main()
        if summary is not None:
            summary.append(summary_path.read_text())
    return code, out.getvalue(), [call.args[0] for call in run.call_args_list]


def done(stdout: str, returncode: int = 1, stderr: str = "") -> subprocess.CompletedProcess:
    return subprocess.CompletedProcess([], returncode, stdout=stdout, stderr=stderr)


class HeaderTests(unittest.TestCase):
    def test_reads_module_keyword_and_import_lines(self):
        head = check.header(SOURCES["MathlibExt/A.lean"])
        self.assertTrue(head.is_module)
        self.assertEqual(head.imports, {
            8: "public import Mathlib.Order.Basic",
            9: "import Mathlib.Tactic.Ring",
            10: "import Mathlib.Tactic.Linarith",
            11: "public meta import MathlibExt.C",
            12: "import all MathlibExt.E",
        })

    def test_non_module_file(self):
        head = check.header(SOURCES["MathlibExt/B.lean"])
        self.assertFalse(head.is_module)
        self.assertEqual(sorted(head.imports), [1, 2])

    def test_header_ends_at_the_first_command(self):
        head = check.header("module\n\npublic import A\npublic section\nimport B\n")
        self.assertEqual(head.imports, {3: "public import A"})


class ParseTests(unittest.TestCase):
    def test_parses_removals_and_additions(self):
        removals, adds = check.parse_output(MODULE_OUTPUT)
        self.assertEqual(removals, [check.Removal("MathlibExt/A.lean", 9, 1),
                                    check.Removal("MathlibExt/A.lean", 10, 1)])
        self.assertEqual(adds, {"MathlibExt/D.lean": ["public import Mathlib.Tactic.TypeStar"],
                                "MathlibExt/A.lean": ["import Mathlib.Tactic.Linarith.Frontend"]})


class MainTests(unittest.TestCase):
    def test_keeps_only_removals_on_added_import_lines(self):
        code, out, calls = run_main([done(MODULE_OUTPUT), done(NONMODULE_OUTPUT)])
        self.assertEqual(code, 1)
        self.assertIn("::error file=MathlibExt/A.lean,line=9,col=1,"
                      "title=unused import%2C with replacements::", out)
        self.assertNotIn("A.lean,line=10", out)  # an import that the change does not add
        self.assertNotIn("D.lean", out)  # `add` suggestions are not reported
        self.assertIn("::error file=MathlibExt/B.lean,line=2,col=1,title=unused import::", out)

    def test_routes_files_by_module_system(self):
        _, _, calls = run_main([done(MODULE_OUTPUT), done(NONMODULE_OUTPUT)])
        self.assertEqual(len(calls), 2)
        module_call, nonmodule_call = calls
        self.assertTrue(module_call[0].endswith("/agitate"))
        self.assertEqual(module_call[1:], ["--keep-public", "--add-public", "--keep-implied",
                                           "--keep-prefix", "--gh-style",
                                           "--only", "MathlibExt.A", "MathlibExt.A"])
        self.assertTrue(nonmodule_call[0].endswith("/agitate-nonmodule"))
        self.assertEqual(nonmodule_call[1:], ["--keep-implied", "--keep-prefix", "--gh-style",
                                              "--only", "MathlibExt.B", "MathlibExt.B"])

    def test_names_the_replacements_that_agitate_suggests(self):
        _, out, _ = run_main([done(MODULE_OUTPUT), done(NONMODULE_OUTPUT)])
        self.assertIn("agitate finds `import Mathlib.Tactic.Ring` unused here", out)
        self.assertIn("also suggests importing `import Mathlib.Tactic.Linarith.Frontend`", out)
        self.assertIn("agitate finds `import MathlibExt.Marked.Iso` unused here", out)
        self.assertNotIn("Marked.Iso` unused here. Remove it, or mark it `-- shake: keep` if it "
                         "is needed in a way that .olean files do not record (such as `open` of "
                         "a namespace). agitate also", out)

    def test_report_only_annotates_and_passes(self):
        summary: list[str] = []
        code, out, _ = run_main([done(MODULE_OUTPUT), done(NONMODULE_OUTPUT)],
                                extra=["--report-only"], summary=summary)
        self.assertEqual(code, 0)
        self.assertIn("| unused import | 1 |", summary[0])
        self.assertIn("::warning file=MathlibExt/A.lean,line=9,col=1,", out)

    def test_passes_when_agitate_suggests_nothing(self):
        summary: list[str] = []
        code, out, _ = run_main([done("", 0), done("", 0)], summary=summary)
        self.assertEqual(code, 0)
        self.assertNotIn("::", out)
        self.assertEqual(summary, [""])

    def test_an_unreadable_base_is_a_failure_to_run(self):
        out = io.StringIO()
        with patch.object(check, "changed_files", side_effect=GitError("no such ref: nope")), \
                patch.object(sys, "argv", ["check_unused_imports.py", "--base", "nope"]), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(check.main(), 2)
        self.assertIn("no such ref: nope", out.getvalue())

    def test_skips_agitate_when_no_import_line_is_added(self):
        files = [ChangedFile("MathlibExt/A.lean", "M", frozenset({17}))]
        code, out, calls = run_main([], files)
        self.assertEqual((code, calls), (0, []))
        self.assertIn("adds an import", out)

    def test_an_uncaught_exception_is_a_failure_to_run(self):
        # agitate exits 1 here too, as when it suggests edits.
        failure = done("", 1, "uncaught exception: object file '/x/A.olean' of module "
                              "MathlibExt.A does not exist\n")
        code, _, _ = run_main([failure], extra=["--report-only"])
        self.assertEqual(code, 2)

    def test_an_unexpected_exit_code_is_a_failure_to_run(self):
        code, _, _ = run_main([done("", 134)], extra=["--report-only"])
        self.assertEqual(code, 2)

    def test_a_toolchain_mismatch_is_a_failure_to_run(self):
        code, _, calls = run_main([], toolchain="leanprover/lean4:v4.0.0\n")
        self.assertEqual((code, calls), (2, []))

    def test_a_missing_agitate_build_is_a_failure_to_run(self):
        code, _, calls = run_main([], agitate_dir=False)
        self.assertEqual((code, calls), (2, []))

    def test_nothing_to_check(self):
        code, out, calls = run_main([], files=[])
        self.assertEqual((code, calls), (0, []))
        self.assertIn("No Lean file", out)


if __name__ == "__main__":
    unittest.main()
