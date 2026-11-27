#!/usr/bin/env python3
"""Regressions for scripts/lean_changes.py; standard library and git only, no Lean.

Run with: python3 -m unittest discover -s scripts -p test_lean_changes.py
"""

from __future__ import annotations

import io
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

import lean_changes
import linters_self_test
from lean_changes import AggregatorError, ChangedFile, GitError

DIFF = """\
diff --git a/MathlibExt/A.lean b/MathlibExt/A.lean
index 1111111..2222222 100644
--- a/MathlibExt/A.lean
+++ b/MathlibExt/A.lean
@@ -2 +2 @@ theorem a
-old
+new
@@ -5,0 +6,2 @@ theorem b
+added one
+added two
@@ -9,3 +10,0 @@ theorem c
-gone
-gone
-gone
diff --git a/MathlibExt/New.lean b/MathlibExt/New.lean
new file mode 100644
--- /dev/null
+++ b/MathlibExt/New.lean
@@ -0,0 +1,3 @@
+module
+
+theorem t : True := trivial
"""

# An added line `++ [2]` is shown as `+++ [2]`, like a file header.
PLUS_DIFF = """\
diff --git a/MathlibExt/A.lean b/MathlibExt/A.lean
--- a/MathlibExt/A.lean
+++ b/MathlibExt/A.lean
@@ -1,0 +2 @@ def xs
+++ [2]
@@ -4,0 +6 @@ def ys
+theorem bad : True := by trivial ; trivial
"""

QUOTED_DIFF = """\
diff --git "a/MathlibExt/Caf\\303\\251.lean" "b/MathlibExt/Caf\\303\\251.lean"
--- "a/MathlibExt/Caf\\303\\251.lean"
+++ "b/MathlibExt/Caf\\303\\251.lean"
@@ -1,0 +2 @@
+theorem t : True := trivial
"""

NO_NEWLINE_DIFF = """\
diff --git a/MathlibExt/A.lean b/MathlibExt/A.lean
--- a/MathlibExt/A.lean
+++ b/MathlibExt/A.lean
@@ -3 +3,2 @@
-end
\\ No newline at end of file
+end
+
@@ -7,0 +9 @@
+theorem late : True := trivial
"""


def git(cwd: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@example.com", *args],
                   cwd=cwd, check=True, capture_output=True)


def repository(files: dict[str, str]) -> tempfile.TemporaryDirectory:
    """A git repository on branch `main` whose one commit holds `files`."""
    tmp = tempfile.TemporaryDirectory()
    root = Path(tmp.name)
    git(root, "init", "-q", "-b", "main")
    write(root, files)
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", "base")
    git(root, "checkout", "-q", "-b", "change")
    return tmp


def write(root: Path, files: dict[str, str]) -> None:
    for path, text in files.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text, encoding="utf-8")


def commit(root: Path) -> None:
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", "change")


class ParseTests(unittest.TestCase):
    def test_parse_diff_collects_added_lines(self):
        self.assertEqual(lean_changes.parse_diff(DIFF), {
            "MathlibExt/A.lean": frozenset({2, 6, 7}),
            "MathlibExt/New.lean": frozenset({1, 2, 3}),
        })

    def test_an_added_line_that_looks_like_a_header_is_an_added_line(self):
        self.assertEqual(lean_changes.parse_diff(PLUS_DIFF), {"MathlibExt/A.lean": frozenset({2, 6})})

    def test_quoted_paths_are_unquoted(self):
        self.assertEqual(lean_changes.parse_diff(QUOTED_DIFF),
                         {"MathlibExt/Café.lean": frozenset({2})})

    def test_no_newline_markers_do_not_end_a_hunk(self):
        self.assertEqual(lean_changes.parse_diff(NO_NEWLINE_DIFF),
                         {"MathlibExt/A.lean": frozenset({3, 4, 9})})

    def test_unquote(self):
        self.assertEqual(lean_changes.unquote('"a\\tb\\\\c\\"d\\303\\251"'), 'a\tb\\c"dé')
        self.assertEqual(lean_changes.unquote("b/plain.lean"), "b/plain.lean")

    def test_parse_name_status_handles_renames(self):
        text = "M\0MathlibExt/A.lean\0R087\0MathlibExt/B.lean\0MathlibExt/C.lean\0A\0Domains/D.lean\0"
        self.assertEqual(lean_changes.parse_name_status(text), {
            "MathlibExt/A.lean": ("M", None), "MathlibExt/C.lean": ("R", "MathlibExt/B.lean"),
            "Domains/D.lean": ("A", None)})

    def test_changed_file_module_library_and_base_path(self):
        file = ChangedFile("CSLibExt/Algorithms/Sort.lean", "M", frozenset())
        self.assertEqual(file.library, "CSLibExt")
        self.assertEqual(file.module, "CSLibExt.Algorithms.Sort")
        self.assertEqual(file.base_path, "CSLibExt/Algorithms/Sort.lean")
        self.assertEqual(ChangedFile("MathlibExt/C.lean", "R", frozenset(), "MathlibExt/B.lean")
                         .base_path, "MathlibExt/B.lean")
        self.assertIsNone(ChangedFile("MathlibExt/D.lean", "A", frozenset()).base_path)

    def test_annotation_escapes_properties_and_message(self):
        self.assertEqual(
            lean_changes.annotation("warning", "MathlibExt/A,B.lean", 3, "linter.x: y",
                                    "50% off\nsecond line", col=7),
            "::warning file=MathlibExt/A%2CB.lean,line=3,col=7,title=linter.x%3A y"
            "::50%25 off%0Asecond line")

    def test_lean_name_quotes_the_components_that_are_not_identifiers(self):
        self.assertEqual(lean_changes.lean_name("MathlibExt.X.Basic'"), "MathlibExt.X.Basic'")
        self.assertEqual(lean_changes.lean_name("MathlibExt.New-Name"), "MathlibExt.«New-Name»")
        self.assertEqual(lean_changes.lean_name("MathlibExt.2D"), "MathlibExt.«2D»")
        self.assertEqual(lean_changes.lean_name("MathlibExt.Sum×Prod"), "MathlibExt.«Sum×Prod»")
        # Lean's identifiers take Latin-1 and Latin Extended-A letters, Greek but λ, Π and Σ,
        # letter-like symbols and subscripts, as `Name.toString` prints them.
        for bare in ("MathlibExt.Système", "MathlibExt.Łukasiewicz", "MathlibExt.αβ",
                     "MathlibExt.ℕSum", "MathlibExt.X₁"):
            self.assertEqual(lean_changes.lean_name(bare), bare)
        self.assertEqual(lean_changes.lean_name("MathlibExt.λCalc"), "MathlibExt.«λCalc»")
        self.assertEqual(lean_changes.lean_name("MathlibExt.₁X"), "MathlibExt.«₁X»")
        for unnameable in ("MathlibExt.A«B", "MathlibExt.A»B", "MathlibExt.A\nB"):
            self.assertIsNone(lean_changes.lean_name(unnameable))
        self.assertEqual(lean_changes.lean_unescaped("MathlibExt.«New-Name»"),
                         "MathlibExt.New-Name")

    def test_inert_breaks_up_workflow_commands_in_github_actions(self):
        text = ("fine\n::error file=A.lean::forged\n  ::add-mask::x\nnot :: a command\n"
                "a deprecation ##[error file=A.lean;line=1]forged, ##[stop-commands]tok and "
                "###[warning]x\rafter a return\r::error::forged\r\n::warning::forged")
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}):
            inert = lean_changes.inert(text)
        self.assertEqual(inert, "fine\n: :error file=A.lean::forged\n  : :add-mask::x\n"
                                "not :: a command\n"
                                "a deprecation ## [error file=A.lean;line=1]forged, "
                                "## [stop-commands]tok and ### [warning]x\nafter a return\n"
                                ": :error::forged\n: :warning::forged")
        self.assertNotIn("##[", inert)
        self.assertFalse(any(line.lstrip().startswith("::") for line in inert.splitlines()))
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "false"}):
            self.assertEqual(lean_changes.inert(text), text)

    def test_a_skipped_path_prints_on_one_inert_line(self):
        files = [ChangedFile("MathlibExt/A\n::error file=B.lean::forged ##[warning]x.lean", "A",
                             frozenset({1}))]
        err = io.StringIO()
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), redirect_stderr(err), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(lean_changes.unnameable(files, annotate=True), files)
        printed = err.getvalue()
        self.assertEqual(printed.count("\n"), 1)
        self.assertIn("MathlibExt/A\\n::error file=B.lean::forged ## [warning]x.lean: Lean "
                      "cannot name the module", printed)

    def test_relative_accepts_absolute_and_relative_paths(self):
        root = Path("/repo")
        self.assertEqual(lean_changes.relative("/repo/MathlibExt/A.lean", root),
                         "MathlibExt/A.lean")
        self.assertEqual(lean_changes.relative("./MathlibExt/A.lean", root), "MathlibExt/A.lean")


class GitTests(unittest.TestCase):
    def test_changed_files_reads_the_change_since_the_merge_base(self):
        with repository({
            "MathlibExt/A.lean": "a\nb\nc\n",
            "MathlibExt/B.lean": "".join(f"line {i}\n" for i in range(10)),
            "MathlibExt/Gone.lean": "x\n",
            "MathlibExtTest/T.lean": "t\n",
        }) as tmp:
            root = Path(tmp)
            write(root, {"MathlibExt/A.lean": "a\nB\nc\nd\n",
                         "MathlibExt/D.lean": "new\nfile\n",
                         "MathlibExtTest/T.lean": "test\n",
                         "MathlibExt/notes.md": "not Lean\n"})
            git(root, "mv", "MathlibExt/B.lean", "MathlibExt/C.lean")
            write(root, {"MathlibExt/C.lean": "".join(f"line {i}\n" for i in range(9)) + "changed\n"})
            (root / "MathlibExt/Gone.lean").unlink()
            commit(root)
            files = lean_changes.changed_files("main", cwd=root)
            deleted = lean_changes.deleted_files("main", cwd=root)
            old = lean_changes.base_text("main", "MathlibExt/B.lean", cwd=root)
            missing = lean_changes.base_text("main", "MathlibExt/D.lean", cwd=root)
        self.assertEqual(files, [
            ChangedFile("MathlibExt/A.lean", "M", frozenset({2, 4})),
            ChangedFile("MathlibExt/C.lean", "R", frozenset({10}), "MathlibExt/B.lean"),
            ChangedFile("MathlibExt/D.lean", "A", frozenset({1, 2})),
        ])
        self.assertEqual(deleted, ["MathlibExt/Gone.lean"])
        self.assertTrue(old.startswith("line 0\n"))
        self.assertIsNone(missing)

    def test_a_later_hunk_after_an_added_plus_plus_line_is_kept(self):
        with repository({"MathlibExt/A.lean": "".join(f"line {i}\n" for i in range(1, 6))}) as tmp:
            root = Path(tmp)
            lines = [f"line {i}" for i in range(1, 6)]
            lines.insert(1, "++ [2]")
            lines.insert(5, "theorem bad : True := by trivial ; trivial")
            write(root, {"MathlibExt/A.lean": "\n".join(lines) + "\n"})
            commit(root)
            files = lean_changes.changed_files("main", cwd=root)
        self.assertEqual(files, [ChangedFile("MathlibExt/A.lean", "M", frozenset({2, 6}))])

    def test_non_ascii_paths_keep_their_added_lines(self):
        with repository({"MathlibExt/Café.lean": "a\n", "MathlibExt/Ünï.lean": "x\ny\n"}) as tmp:
            root = Path(tmp)
            write(root, {"MathlibExt/Café.lean": "a\nb\n"})
            git(root, "mv", "MathlibExt/Ünï.lean", "MathlibExt/Ñame.lean")
            write(root, {"MathlibExt/Ñame.lean": "x\ny\nz\n"})
            commit(root)
            files = lean_changes.changed_files("main", cwd=root)
        self.assertEqual(files, [
            ChangedFile("MathlibExt/Café.lean", "M", frozenset({2})),
            ChangedFile("MathlibExt/Ñame.lean", "R", frozenset({3}), "MathlibExt/Ünï.lean"),
        ])


class FailureTests(unittest.TestCase):
    def test_an_unknown_base_is_a_git_error_that_names_it(self):
        with repository({"MathlibExt/A.lean": "a\n"}) as tmp:
            with self.assertRaises(GitError) as raised:
                lean_changes.changed_files("no-such-base", cwd=Path(tmp))
        self.assertIn("no-such-base", str(raised.exception))

    def test_guarded_turns_a_git_error_into_exit_2(self):
        def main() -> int:
            raise GitError("`git diff` failed: unknown revision no-such-base")

        err = io.StringIO()
        with redirect_stderr(err):
            self.assertEqual(lean_changes.guarded(main)(), 2)
        self.assertIn("no-such-base", err.getvalue())
        self.assertEqual(lean_changes.guarded(lambda: 1)(), 1)


class SummaryTests(unittest.TestCase):
    def test_the_summary_is_written_only_in_github_actions(self):
        with tempfile.TemporaryDirectory() as tmp:
            summary = Path(tmp, "summary.md")
            summary.write_text("")
            with patch.dict("os.environ", {"GITHUB_STEP_SUMMARY": str(summary),
                                           "GITHUB_ACTIONS": "false"}):
                lean_changes.write_summary("outside\n")
            with patch.dict("os.environ", {"GITHUB_STEP_SUMMARY": str(summary),
                                           "GITHUB_ACTIONS": "true"}):
                lean_changes.write_summary("inside\n")
            self.assertEqual(summary.read_text(), "inside\n")

    def test_the_check_tests_leave_the_job_summary_alone(self):
        # The tests run the checks on fixtures with GITHUB_ACTIONS set; none may write here.
        with tempfile.TemporaryDirectory() as tmp:
            summary = Path(tmp, "summary.md")
            summary.write_text("")
            env = {**os.environ, "GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(summary)}
            scripts = str(lean_changes.ROOT / "scripts")
            result = subprocess.run(
                [sys.executable, "-m", "unittest", "discover", "-s", scripts,
                 "-p", "test_check_*.py"], env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr[-2000:])
            self.assertEqual(summary.read_text(), "")

    def test_the_self_test_runs_the_checks_outside_github_actions(self):
        outer = {"GITHUB_STEP_SUMMARY": "/summary", "GITHUB_ACTIONS": "true"}
        with patch.dict("os.environ", outer):
            env = linters_self_test.child_env()
        self.assertNotIn("GITHUB_STEP_SUMMARY", env)
        self.assertEqual(env["GITHUB_ACTIONS"], "false")


class AggregatorTests(unittest.TestCase):
    def test_writes_one_plain_aggregator_per_library_and_removes_it(self):
        files = [ChangedFile("MathlibExt/X/A.lean", "M", frozenset({1})),
                 ChangedFile("MathlibExt/B.lean", "A", frozenset({1})),
                 ChangedFile("Domains/C.lean", "M", frozenset({2}))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            (root / "Domains").mkdir()
            with lean_changes.aggregators(files, cwd=root) as names:
                self.assertEqual(names, ["Domains.LintChanged", "MathlibExt.LintChanged"])
                self.assertEqual((root / "MathlibExt/LintChanged.lean").read_text(),
                                 "import MathlibExt.B\nimport MathlibExt.X.A\n")
                self.assertEqual((root / "Domains/LintChanged.lean").read_text(),
                                 "import Domains.C\n")
            self.assertEqual(sorted(os.listdir(root / "MathlibExt")), [])

    def test_quotes_module_names_and_leaves_out_files_lean_cannot_name(self):
        files = [ChangedFile("MathlibExt/X/New-Name.lean", "A", frozenset({1})),
                 ChangedFile("MathlibExt/B.lean", "A", frozenset({1})),
                 ChangedFile("MathlibExt/C«D.lean", "A", frozenset({1}))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            err = io.StringIO()
            with redirect_stderr(err), lean_changes.aggregators(files, cwd=root) as names:
                self.assertEqual(names, ["MathlibExt.LintChanged"])
                self.assertEqual((root / "MathlibExt/LintChanged.lean").read_text(),
                                 "import MathlibExt.B\nimport MathlibExt.X.«New-Name»\n")
            self.assertIn("MathlibExt/C«D.lean: Lean cannot name the module", err.getvalue())

    def test_refuses_to_overwrite_a_module(self):
        files = [ChangedFile("MathlibExt/B.lean", "A", frozenset({1}))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/LintChanged.lean").write_text("theorem kept : True := trivial\n")
            with self.assertRaises(AggregatorError):
                with lean_changes.aggregators(files, cwd=root):
                    pass
            self.assertIn("kept", (root / "MathlibExt/LintChanged.lean").read_text())


class BuildTests(unittest.TestCase):
    def run_build(self, files, returncode=0, exists=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "MathlibExt").mkdir()
            if exists:
                (root / "MathlibExt/LintChanged.lean").write_text("theorem kept : True := trivial\n")
            result = subprocess.CompletedProcess([], returncode)
            with patch.object(lean_changes, "changed_files", return_value=files), \
                    patch.object(lean_changes.subprocess, "run", return_value=result) as run, \
                    redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                code = lean_changes.build("main", cwd=root)
            return code, run

    def test_builds_the_aggregators(self):
        code, run = self.run_build([ChangedFile("MathlibExt/A.lean", "M", frozenset({1}))])
        self.assertEqual(code, 0)
        self.assertEqual(run.call_args.args[0], ["lake", "build", "MathlibExt.LintChanged"])

    def test_reports_a_failed_build(self):
        code, _ = self.run_build([ChangedFile("MathlibExt/A.lean", "M", frozenset({1}))], 1)
        self.assertEqual(code, 1)

    def test_nothing_to_build(self):
        code, run = self.run_build([])
        self.assertEqual(code, 0)
        run.assert_not_called()

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        code, run = self.run_build([ChangedFile("MathlibExt/A.lean", "M", frozenset({1}))],
                                   exists=True)
        self.assertEqual(code, 2)
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
