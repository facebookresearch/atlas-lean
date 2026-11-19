"""Source-diagnostic regressions; standard library only, never invokes Lean."""

import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from collections.abc import Iterator
from contextlib import AbstractContextManager
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

import source_diagnostics

LIBRARIES = (
    "CSLibExt",
    "CSLibExtTest",
    "MathlibExt",
    "MathlibExtTest",
    "PhyslibExt",
    "PhyslibExtTest",
    "WantedExt",
)
SCANNERS = ("check_duplicate_defs.py", "check_hypothesis_debt.py")


class DiagnosticFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="atlas-source-tests-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write(self, name: str, source: str) -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return path

    def run_scan(
        self, script: str, *roots: Path, report: bool = False
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(ROOT / script),
                *(["--report-only"] if report else []),
                *map(str, roots),
            ],
            capture_output=True,
            text=True,
            timeout=20,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
        )

    def candidates(
        self, *roots: Path, report: bool = False
    ) -> subprocess.CompletedProcess[str]:
        return self.run_scan(SCANNERS[0], *(roots or (self.root,)), report=report)

    def debt(
        self, *roots: Path, report: bool = False
    ) -> subprocess.CompletedProcess[str]:
        return self.run_scan(SCANNERS[1], *(roots or (self.root,)), report=report)

    def assert_candidate(
        self, result: subprocess.CompletedProcess[str], name: str
    ) -> None:
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f"CANDIDATE {name}:", result.stdout)
        self.assertNotIn("semantic-conflict", result.stdout)
        self.assertNotIn("PASS", result.stdout)


class SourceDiagnosticsTests(DiagnosticFixture):
    def test_candidates_across_roots(self) -> None:
        self.write("left/a.lean", "def Foo (x : Nat) : Nat := x + 1\n")
        self.write("right/b.lean", "def Foo (x : Nat) : Nat := x + 1\n")
        result = self.candidates(self.root / "left", self.root / "right")
        self.assert_candidate(result, "Foo")
        self.assertIn("Scanned files: 2", result.stdout)

    def test_later_alias_cannot_hide_previous_abbreviation(self) -> None:
        self.write(
            "a.lean", "abbrev Foo (x : Nat) : Nat := x + 1\nabbrev Later := Nat\n"
        )
        self.write("b.lean", "abbrev Foo (x : Nat) : Nat := x + 1\n")
        self.assert_candidate(self.candidates(), "Foo")

    def test_renamed_dependent_binders_are_text_only(self) -> None:
        signatures = ("(n : Nat) (i : Fin n) : Fin n", "(m : Nat) (j : Fin m) : Fin m")
        for name, signature, body in zip(("a", "b"), signatures, ("i", "j")):
            self.write(f"{name}.lean", f"def Foo {signature} := {body}\n")
        result = self.candidates()
        self.assert_candidate(result, "Foo")
        for signature in signatures:
            self.assertIn(signature, result.stdout)
        self.assertNotIn("DIFFERENT", result.stdout)
        self.assertNotIn("same signature", result.stdout)

    def test_debt_ignores_comment_and_string_baseline(self) -> None:
        self.write(
            "a.lean",
            "/- theorem_wanted commented : True -/\n"
            'def text : String := "def_wanted quoted : Nat"\n'
            "theorem_wanted genuine : True\n",
        )
        result = self.debt(report=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Total debt items: 1", result.stdout)
        self.assertIn("theorem_wanted genuine", result.stdout)
        self.assertNotIn("commented", result.stdout)
        self.assertNotIn("quoted", result.stdout)

    def test_direct_alias_excluded_but_typed_and_parameterized_retained(self) -> None:
        self.write("a.lean", "def Foo : Nat := 1\ndef Bar (n : Nat) := n\n")
        self.write(
            "b.lean", "abbrev Foo : Nat := A.Foo\nabbrev Bar (n : Nat) := A.Bar n\n"
        )
        self.write("c.lean", "abbrev Foo := A.Foo\n")
        result = self.candidates()
        self.assert_candidate(result, "Foo")
        self.assertIn("CANDIDATE Bar:", result.stdout)
        self.assertNotIn(str(self.root / "c.lean"), result.stdout)
        self.assertIn("direct aliases excluded: 1", result.stdout)

    def test_alias_continuations_and_literals_are_retained(self) -> None:
        for body in (
            "A.Foo\n  + 1",
            'A.Foo "argument"',
            "(A.Foo)",
            "by exact A.Foo",
            "_",
            "sorry",
            "by",
            "Nat",
        ):
            with self.subTest(body=body):
                self.write("a.lean", f"abbrev Foo := {body}\n")
                self.write("b.lean", "def Foo := 1\n")
                self.assert_candidate(self.candidates(), "Foo")

    def test_nested_comments_escaped_literals_and_primed_names(self) -> None:
        hidden = (
            "/- outer /- inner -/\ndef Foo := 0\n"
            "theorem_wanted fake : True\n-/\n"
            'def text := "escaped \\"\ndef Foo := 0\n'
            'def_wanted fake : Nat"\n'
            "def char := '\\''\n"
        )
        self.write("a.lean", hidden + "def Foo' := 1\n")
        self.write("b.lean", "def Foo' := 2\ndef_wanted real : Nat\n")
        result = self.candidates()
        self.assert_candidate(result, "Foo'")
        self.assertNotIn("CANDIDATE Foo:", result.stdout)
        self.assertIn("Total debt items: 1", self.debt(report=True).stdout)

    def test_unicode_and_quoted_names_preserve_short_component(self) -> None:
        for name in ("α₁", "pathTo?", "get!", "«two words»", "«Foo.Bar»"):
            with self.subTest(name=name):
                self.write("a.lean", f"def A.{name} : Nat := 1\n")
                self.write("b.lean", f"def B.{name} : Nat := 2\n")
                self.assert_candidate(self.candidates(), name)
        self.write("wanted.lean", "theorem_wanted «debt.α» : True\n")
        self.assertIn("theorem_wanted «debt.α»", self.debt(report=True).stdout)

    def test_long_multiline_signature_keeps_binder_defaults_and_tail(self) -> None:
        signature = (
            "(n : Nat := 3)\n"
            + "\n".join(f"    (x{i} : Fin n)" for i in range(80))
            + " : Fin n"
        )
        self.write("a.lean", f"def Foo {signature} := x79\n")
        self.write("b.lean", "def Foo (m : Nat) : Fin m := 0\n")
        result = self.candidates()
        self.assert_candidate(result, "Foo")
        self.assertIn("(x79 : Fin n)", result.stdout)
        self.assertIn("(n : Nat := 3)", result.stdout)

    def test_equations_attributes_and_modifiers_remain_candidates(self) -> None:
        self.write(
            "a.lean", "@[simp] private noncomputable def Foo : Nat → Nat\n  | n => n\n"
        )
        self.write("b.lean", "@[simp]\nprotected def Foo (n : Nat) : Nat := n\n")
        self.assert_candidate(self.candidates(), "Foo")

    def test_unrecognized_header_kept_as_candidate_without_type_claim(self) -> None:
        self.write("a.lean", "def Foo strange_custom_header\n")
        self.write("b.lean", "def Foo : Nat := 0\n")
        result = self.candidates()
        self.assert_candidate(result, "Foo")
        self.assertIn("strange_custom_header", result.stdout)

    def test_debt_requires_declaration_shape_and_drops_prose(self) -> None:
        self.write(
            "a.lean",
            "-- hypothesis debt, L1 capstone, assume Foo\n"
            'def message := "assume Bar"\n'
            "#check theorem_wanted\n#check proof_wanted\n"
            "def useToken := theorem_wanted\n"
            "@[simp] private theorem_wanted α : True\n"
            "def_wanted β (n : Nat) : Nat\n",
        )
        result = self.debt(report=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Total debt items: 2", result.stdout)
        self.assertNotIn("DEBT-MARKER", result.stdout)

    def test_distinct_names_have_zero_findings_with_nonzero_counts(self) -> None:
        self.write("a.lean", "def Foo := 0\n")
        self.write("b.lean", "def Bar := 0\n")
        for script in SCANNERS:
            result = self.run_scan(script, self.root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Scanned files: 2", result.stdout)

    def test_overlap_repeated_roots_and_hardlinks_count_files_once(self) -> None:
        a = self.write("inner/a.lean", "def Foo := 0\ntheorem_wanted debt : True\n")
        os.link(a, self.root / "linked.lean")
        for script in SCANNERS:
            result = self.run_scan(
                script, self.root, self.root / "inner", self.root, report=True
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Scanned files: 1", result.stdout)
            self.assertNotIn("CANDIDATE", result.stdout)
        self.assertIn(
            "Total debt items: 1",
            self.debt(self.root, self.root / "inner", report=True).stdout,
        )

    def test_no_arguments_missing_empty_and_nondirectory_roots_fail(self) -> None:
        empty = self.root / "empty"
        empty.mkdir()
        file = self.write("valid/a.lean", "def Foo := 0\n")
        for script in SCANNERS:
            for roots in (
                (),
                (self.root / "missing",),
                (empty,),
                (file,),
                (self.root / "valid", empty),
                (self.root / "valid", self.root / "missing"),
            ):
                with self.subTest(script=script, roots=roots):
                    result = self.run_scan(script, *roots, report=True)
                    self.assertEqual(
                        result.returncode, 2, result.stdout + result.stderr
                    )
                    self.assertNotIn("Scanned files:", result.stdout)

    def test_excluded_directories_are_pruned_and_explicit_roots_rejected(self) -> None:
        self.write("a.lean", "def Foo := 0\n")
        for excluded in (".lake", ".git", "v1", "dependencies"):
            # Empty forbidden directories: the test never traverses .lake.
            (self.root / excluded).mkdir()
        for script in SCANNERS:
            result = self.run_scan(script, self.root, report=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Scanned files: 1", result.stdout)
            for excluded in (".lake", ".git", "v1", "dependencies"):
                result = self.run_scan(script, self.root / excluded, report=True)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn("excluded", result.stderr)

    def test_walk_never_enters_excluded_or_symlink_directories(self) -> None:
        source = self.write("real/a.lean", "def Foo := 0\n")
        for excluded in (".lake", ".git", "v1", "dependencies"):
            (self.root / excluded).mkdir()
        (self.root / "linked").symlink_to(self.root / "real", target_is_directory=True)
        scandir = os.scandir
        entered = []

        def guarded_scandir(
            directory: Path,
        ) -> AbstractContextManager[Iterator[os.DirEntry[str]]]:
            self.assertNotIn(
                directory.name, {".lake", ".git", "v1", "dependencies", "linked"}
            )
            entered.append(directory)
            return scandir(directory)

        with patch.object(source_diagnostics.os, "scandir", guarded_scandir):
            self.assertEqual(source_diagnostics.lean_files([self.root]), [source])
        self.assertEqual(entered, [self.root, self.root / "real"])

    def test_unreadable_subdirectory_is_fatal(self) -> None:
        self.write("readable.lean", "def Foo := 0\n")
        hidden = self.write("locked/a.lean", "def Bar := 0\n").parent
        hidden.chmod(0)
        self.addCleanup(hidden.chmod, 0o700)
        for script in SCANNERS:
            result = self.run_scan(script, self.root, report=True)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("SCAN ERROR", result.stderr)

    def test_symlink_directories_pruned_and_explicit_symlink_paths_fail(self) -> None:
        self.write("real/a.lean", "def Foo := 0\n")
        (self.root / "loop").symlink_to(self.root, target_is_directory=True)
        (self.root / "alias").symlink_to(self.root / "real", target_is_directory=True)
        for script in SCANNERS:
            result = self.run_scan(script, self.root, report=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Scanned files: 1", result.stdout)
            result = self.run_scan(script, self.root / "alias", report=True)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_bad_utf8_unreadable_and_nonregular_sources_fail(self) -> None:
        source = self.write("bad.lean", "def Foo := 0\n")
        for mode in ("utf8", "unreadable", "fifo", "symlink"):
            with self.subTest(mode=mode):
                source.unlink()
                if mode == "fifo":
                    os.mkfifo(source)
                elif mode == "symlink":
                    source.symlink_to(self.root / "missing")
                else:
                    source.write_bytes(b"\xff" if mode == "utf8" else b"def Foo := 0\n")
                    if mode == "unreadable":
                        source.chmod(0)
                for script in SCANNERS:
                    result = self.run_scan(script, self.root, report=True)
                    self.assertEqual(
                        result.returncode, 2, result.stdout + result.stderr
                    )
                    self.assertIn("SCAN ERROR", result.stderr)
                if mode == "unreadable":
                    source.chmod(0o600)

    def test_malformed_lexical_input_or_names_fail_visibly(self) -> None:
        for source in (
            "/- unfinished",
            'def Foo := "unfinished',
            "def «unfinished : Nat := 0\n",
            "def : Nat := 0\n",
            "def_wanted : Nat\n",
            "def «quoted--name» := 0\n",
            'def text := r#"raw"#\n',
            "def Foo (x : Nat := 1\n",
            "def Foo'x' : Nat := 1\n",
            "class inductive Foo where\n  | mk : Foo\n",
        ):
            with self.subTest(source=source):
                self.write("a.lean", source)
                for script in SCANNERS:
                    result = self.run_scan(script, self.root, report=True)
                    self.assertEqual(
                        result.returncode, 2, result.stdout + result.stderr
                    )
                    self.assertIn("SCAN ERROR", result.stderr)

    def test_report_mode_does_not_hide_positive_findings(self) -> None:
        self.write("a.lean", "def Foo := 0\ntheorem_wanted debt : True\n")
        self.write("b.lean", "def Foo := 1\n")
        for script, finding in zip(SCANNERS, ("CANDIDATE Foo:", "DEBT")):
            result = self.run_scan(script, self.root, report=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(finding, result.stdout)
            self.assertIn("Scanned files: 2", result.stdout)

    def test_wanted_findings_fail_without_report_mode(self) -> None:
        self.write("a.lean", "theorem_wanted debt : True\n")
        result = self.debt()
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("Total debt items: 1", result.stdout)

    def test_empty_lean_file_does_not_satisfy_required_declarations(self) -> None:
        self.write("a.lean", "-- No declarations.\n")
        for script in SCANNERS:
            result = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / script),
                    "--report-only",
                    "--require-declarations",
                    str(self.root),
                ],
                capture_output=True,
                text=True,
                timeout=20,
            )
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("no recognized declarations", result.stderr)

    def test_structure_class_inductive_and_universe_headers(self) -> None:
        source = (
            "structure Box where\n  x : Nat\n"
            "class HasBox (α : Type) where\n  box : α\n"
            "inductive Choice where\n  | left | right\n"
            "def Id.{u} (α : Type u) := α\n"
        )
        self.write("a.lean", source)
        self.write("b.lean", source)
        result = self.candidates()
        for name in ("Box", "HasBox", "Choice", "Id"):
            self.assert_candidate(result, name)
        self.assertIn("Candidate groups: 4", result.stdout)


class WorkflowTests(DiagnosticFixture):
    # Use the actual run block, with miniature libraries and an isolated test
    # sentinel to avoid recursively running this workflow test inside itself.
    def workflow_command(self) -> str:
        workflow = (
            ROOT.parent / ".github/workflows/source-diagnostics.yml"
        ).read_text()
        self.assertIn("  pull_request:\n", workflow)
        self.assertNotIn("pull_request_target", workflow)
        self.assertIn("permissions:\n  contents: read\n", workflow)
        self.assertIn("persist-credentials: false", workflow)
        current_ci = (ROOT.parent / ".github/workflows/ci.yml").read_text()
        checkout = re.search(r"actions/checkout@[0-9a-f]{40}", workflow)
        self.assertIsNotNone(checkout)
        self.assertIn(checkout.group(), current_ci)
        self.assertNotIn("continue-on-error", workflow)
        self.assertIn('PYTHONDONTWRITEBYTECODE: "1"', workflow)
        blocks = workflow.split("        run: |\n")
        self.assertEqual(len(blocks), 2, "expected one executable workflow block")
        return textwrap.dedent(blocks[1])

    def prepare_workflow(self) -> None:
        scripts = self.root / "scripts"
        (scripts / "bump").mkdir(parents=True)
        for name in (*SCANNERS, "source_diagnostics.py", "bump/pinned_bump.py"):
            shutil.copyfile(ROOT / name, scripts / name)
        self.write(
            "scripts/test_week2_ci.py",
            "import unittest\n"
            "class Sentinel(unittest.TestCase):\n"
            "    def test_focused(self):\n"
            "        print('FOCUSED_TEST_EXECUTED')\n",
        )
        for library in LIBRARIES:
            self.write(
                f"{library}/Real.lean", "def Foo := 0\ntheorem_wanted debt : True\n"
            )

    def execute_workflow(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", "-c", self.workflow_command()],
            cwd=self.root,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            capture_output=True,
            text=True,
            timeout=30,
        )

    def test_workflow_executes_focused_tests_and_both_scanners_on_seven_roots(
        self,
    ) -> None:
        self.prepare_workflow()
        result = self.execute_workflow()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("FOCUSED_TEST_EXECUTED", result.stdout)
        self.assertIn("Ran 1 test", result.stderr)
        self.assertEqual(result.stdout.count("Scanned files: 7"), 2)
        self.assertIn("CANDIDATE Foo: same short name in 7 files", result.stdout)
        self.assertIn("Total debt items: 7", result.stdout)

    def test_workflow_propagates_test_failure(self) -> None:
        self.prepare_workflow()
        self.write(
            "scripts/test_week2_ci.py",
            "import unittest\n"
            "class Sentinel(unittest.TestCase):\n"
            "    def test_failure(self):\n"
            "        self.fail('FOCUSED_FAILURE_CONTROL')\n",
        )
        result = self.execute_workflow()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FOCUSED_FAILURE_CONTROL", result.stderr)
        self.assertNotIn("Scanned files:", result.stdout)

    def test_workflow_propagates_each_scanner_failure(self) -> None:
        self.prepare_workflow()
        for script in SCANNERS:
            with self.subTest(script=script):
                self.write(f"scripts/{script}", "raise SystemExit(17)\n")
                result = self.execute_workflow()
                self.assertEqual(result.returncode, 17, result.stdout + result.stderr)
                shutil.copyfile(ROOT / script, self.root / "scripts" / script)

    def test_workflow_propagates_real_input_failure(self) -> None:
        self.prepare_workflow()
        (self.root / "CSLibExt/Real.lean").write_bytes(b"\xff")
        result = self.execute_workflow()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("SCAN ERROR", result.stderr)

    def test_workflow_requires_nonempty_definition_and_wanted_counts(self) -> None:
        self.prepare_workflow()
        for source in ("theorem_wanted debt : True\n", "def Foo := 0\n"):
            with self.subTest(source=source):
                for library in LIBRARIES:
                    self.write(f"{library}/Real.lean", source)
                result = self.execute_workflow()
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn("no recognized declarations", result.stderr)


if __name__ == "__main__":
    unittest.main()
