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
from check_env_linters import Finding
from lean_changes import ROOT, AggregatorError, ChangedFile

A = f"{ROOT}/MathlibExt/A.lean"
B = f"{ROOT}/MathlibExt/B.lean"

# What scripts/lint_declarations.lean prints, in `runLinter`'s format, for modules with findings.
OUTPUT = f"""\
-- Found 9 errors in 24 declarations (plus 32 automatically generated ones) in [MathlibExt.A, MathlibExt.B] with 19 linters

/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:
This linter can be disabled with `@[nolint docBlame]`. -/
-- MathlibExt.A
{A}:9:1: error: X.fresh definition missing documentation string
-- MathlibExt.B
{B}:10:1: error: Y.old definition missing documentation string

/- The `unusedArguments` linter reports:
UNUSED ARGUMENTS.
This linter can be disabled with `@[nolint unusedArguments]`. -/
-- MathlibExt.A
{A}:3:1: error: @X.old 1 unused argument:
  argument 1: (m : ℕ)
{A}:9:1: error: @X.fresh✝ 1 unused argument:
  argument 1: (m : ℕ)

/- The `duplicateStatement` linter reports:
THEOREMS WHOSE STATEMENT ANOTHER THEOREM ALREADY PROVES:
This linter can be disabled with `@[nolint duplicateStatement]`. -/
-- MathlibExt.A
{A}:6:1: error: X.keep has the same statement as `trivial` (in `Init.Core`)
-- MathlibExt.B
{B}:10:1: error: Y.old has the same statement as private `Z.old` (in `MathlibExt.C`)

/- The `simpNF` linter reports:
SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
This linter can be disabled with `@[nolint simpNF]`. -/
-- MathlibExt.A
#check @X.Pt.mk.injEq /- LINTER FAILED:
maximum recursion depth has been reached -/
#check @X.Gone.aux /- LINTER FAILED:
deterministic timeout -/
-- MathlibExt.Unchanged
#check @Z.Q.mk.injEq /- LINTER FAILED:
maximum recursion depth has been reached -/
"""

BASE_A = """\
namespace X

def old (m n : Nat) : Nat := n

@[simp] theorem keep : True := trivial

end X
"""

# Documents `old` (lines 3, 4), adds `fresh` (8-9) and the structure `Pt` (11-13).
HEAD_A = """\
namespace X

/-- Old, now documented. -/
def old (m n : Nat) : Nat := n

@[simp] theorem keep : True := trivial

/-- -/
private def fresh (m n : Nat) : Nat := n

structure Pt where
  x : Nat
  y : Nat

end X
"""

FILES = [ChangedFile("MathlibExt/A.lean", "M", frozenset({3, 8, 9, 10, 11, 12, 13})),
         ChangedFile("MathlibExt/B.lean", "M", frozenset({12}))]

HEAD_B = "namespace Y\n\n" + "\n" * 7 + "def old (m : Nat) : Nat := m\n\nend Y\n"


class ParseTests(unittest.TestCase):
    def test_parses_findings_with_their_linter_module_and_position(self):
        findings = check.parse_run_linter(OUTPUT)
        self.assertEqual([(f.declaration, f.linter, f.module, f.path, f.line) for f in findings], [
            ("X.fresh", "docBlame", "MathlibExt.A", "MathlibExt/A.lean", 9),
            ("Y.old", "docBlame", "MathlibExt.B", "MathlibExt/B.lean", 10),
            ("X.old", "unusedArguments", "MathlibExt.A", "MathlibExt/A.lean", 3),
            ("X.fresh", "unusedArguments", "MathlibExt.A", "MathlibExt/A.lean", 9),
            ("X.keep", "duplicateStatement", "MathlibExt.A", "MathlibExt/A.lean", 6),
            ("Y.old", "duplicateStatement", "MathlibExt.B", "MathlibExt/B.lean", 10),
            ("X.Pt.mk.injEq", "simpNF", "MathlibExt.A", None, None),
            ("X.Gone.aux", "simpNF", "MathlibExt.A", None, None),
            ("Z.Q.mk.injEq", "simpNF", "MathlibExt.Unchanged", None, None),
        ])
        self.assertEqual(findings[3].message, "1 unused argument:\n  argument 1: (m : ℕ)")
        self.assertEqual(findings[4].message,
                         "has the same statement as `trivial` (in `Init.Core`)")
        self.assertEqual(findings[6].message,
                         "LINTER FAILED:\nmaximum recursion depth has been reached")

    def test_declaration_names(self):
        self.assertEqual(check.declaration_name("@Foo.bar✝¹ 1 unused argument:"),
                         ("Foo.bar", "1 unused argument:"))
        self.assertEqual(check.declaration_name("X.«weird name» definition missing"),
                         ("X.weird name", "definition missing"))


SOURCE = """\
/-
Copyright
-/
module

public import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- Doc. -/
@[simp,
  norm_cast]
protected theorem foo (n : Nat) : n = n := rfl

private def bar.{u} (α : Sort u) : Nat := 1

instance (priority := 100) instNamed : Inhabited Nat := ⟨0⟩

instance : Inhabited Bool := ⟨true⟩

noncomputable section

structure Pt (α : Type) where
  /-- x coordinate -/
  x : α
  y z : α
  mk' ::

end

class inductive Cls
  | one
  | two (n : Nat)

theorem _root_.Nat.rootThm : True := trivial

alias ⟨fooL, _⟩ := foo

set_option linter.style.longLine false in
lemma «weird name» : True := trivial

example : True := trivial

end MetaMathlibExt

def outside : Nat := 2 -- def notADeclaration
/- theorem alsoNot : True -/
"""


class IndexTests(unittest.TestCase):
    def test_names_declarations_in_their_namespaces(self):
        index = check.index_source(SOURCE)
        self.assertEqual({line: sorted(names) for line, names in index.names_at.items()}, {
            13: ["MetaMathlibExt.foo"],
            15: ["MetaMathlibExt.bar"],
            17: ["MetaMathlibExt.instNamed"],
            23: ["MetaMathlibExt.Pt", "MetaMathlibExt.Pt.mk", "MetaMathlibExt.Pt.mk'"],
            25: ["MetaMathlibExt.Pt.x"],
            26: ["MetaMathlibExt.Pt.y", "MetaMathlibExt.Pt.z"],
            31: ["MetaMathlibExt.Cls"],
            32: ["MetaMathlibExt.Cls.one"],
            33: ["MetaMathlibExt.Cls.two"],
            35: ["Nat.rootThm"],
            37: ["MetaMathlibExt.fooL"],
            40: ["MetaMathlibExt.weird name"],
            46: ["outside"],
        })

    def test_the_declaring_line_skips_docstrings_attributes_and_modifiers(self):
        index = check.index_source(SOURCE)
        self.assertEqual(index.declaration_line(10), 13)
        self.assertEqual(index.declaration_line(11), 13)
        self.assertEqual(index.declaration_line(39), 40)
        self.assertEqual(index.declaration_line(24), 25)
        self.assertEqual(index.declaration_line(17), 17)

    def test_unlexable_sources_fall_back_to_the_reported_line(self):
        index = check.index_source('def s := "unterminated\n')
        self.assertIsNone(index.code)
        self.assertEqual(index.declaration_line(1), 1)


class PlaceTests(unittest.TestCase):
    def setUp(self):
        self.files = {file.path: file for file in FILES}
        self.indexes = {"MathlibExt/A.lean": check.index_source(HEAD_A),
                        "MathlibExt/B.lean": check.index_source(HEAD_B)}
        self.base = check.index_source(BASE_A).names | {"Y.old"}

    def place(self, finding: Finding, base=None):
        return check.place(finding, self.files, self.indexes,
                           self.base if base is None else base)

    def test_a_declaration_that_only_gains_a_docstring_is_not_added(self):
        placement = self.place(Finding("X.old", "unusedArguments", "", "MathlibExt.A",
                                       "MathlibExt/A.lean", 3, 1))
        self.assertFalse(placement.added)

    def test_a_declaration_that_only_gains_an_attribute_is_not_added(self):
        head = "namespace X\n\n@[simp]\ntheorem keep : True := trivial\n\nend X\n"
        files = {"MathlibExt/A.lean": ChangedFile("MathlibExt/A.lean", "M", frozenset({3}))}
        placement = check.place(Finding("X.keep", "simpNF", "", "MathlibExt.A",
                                        "MathlibExt/A.lean", 3, 1),
                                files, {"MathlibExt/A.lean": check.index_source(head)},
                                {"X.keep"})
        self.assertFalse(placement.added)

    def test_a_new_declaration_is_added(self):
        placement = self.place(Finding("X.fresh", "docBlame", "", "MathlibExt.A",
                                       "MathlibExt/A.lean", 8, 1))
        self.assertTrue(placement.added)
        self.assertEqual((placement.path, placement.line, placement.col),
                         ("MathlibExt/A.lean", 8, 1))

    def test_an_edited_declaration_line_of_an_existing_declaration_is_not_added(self):
        # B's line 10 declares `Y.old`; the change edits line 10, but Y.old is at the base.
        files = {"MathlibExt/B.lean": ChangedFile("MathlibExt/B.lean", "M", frozenset({10}))}
        placement = check.place(Finding("Y.old", "docBlame", "", "MathlibExt.B",
                                        "MathlibExt/B.lean", 10, 1),
                                files, self.indexes, {"Y.old"})
        self.assertFalse(placement.added)
        placement = check.place(Finding("Y.old", "docBlame", "", "MathlibExt.B",
                                        "MathlibExt/B.lean", 10, 1),
                                files, self.indexes, set())
        self.assertTrue(placement.added)

    def test_a_finding_without_a_position_goes_to_its_enclosing_declaration(self):
        placement = self.place(Finding("X.Pt.mk.injEq", "simpNF", "LINTER FAILED", "MathlibExt.A"))
        self.assertEqual((placement.path, placement.line, placement.col, placement.added),
                         ("MathlibExt/A.lean", 11, None, True))
        placement = self.place(Finding("X.Pt.mk.injEq", "simpNF", "", "MathlibExt.A"),
                               base={"X.Pt.mk"})
        self.assertFalse(placement.added)

    def test_findings_elsewhere_have_no_placement(self):
        self.assertIsNone(self.place(Finding("Z.Q.mk.injEq", "simpNF", "", "MathlibExt.Unchanged")))
        self.assertIsNone(self.place(Finding("X.Gone.aux", "simpNF", "", "MathlibExt.A")))
        self.assertIsNone(self.place(Finding("W.w", "docBlame", "", "MathlibExt.W",
                                             "MathlibExt/W.lean", 1, 1)))


def run_main(outputs: list[tuple[int, str]], files=FILES, build_code: int = 0, extra=(),
             aggregator_error=False) -> tuple[int, str, str]:
    @contextlib.contextmanager
    def fake_aggregators(changed):
        if aggregator_error:
            raise AggregatorError("MathlibExt/LintChanged.lean exists")
        yield ["MathlibExt.LintChanged"]

    results = [subprocess.CompletedProcess([], build_code, stdout="", stderr="")]
    results += [subprocess.CompletedProcess([], code, stdout=text, stderr="")
                for code, text in outputs]
    sources = {"MathlibExt/A.lean": HEAD_A, "MathlibExt/B.lean": HEAD_B}
    bases = {"MathlibExt/A.lean": BASE_A, "MathlibExt/B.lean": HEAD_B}
    out, err = io.StringIO(), io.StringIO()
    with patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "deleted_files", return_value=[]), \
            patch.object(check, "base_text", side_effect=lambda base, path: bases.get(path)), \
            patch.object(check, "read_source", side_effect=lambda path: sources[path]), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", side_effect=results) as run, \
            patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}), \
            patch.object(sys, "argv", ["check_env_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = check.main()
    if files and build_code == 0 and not aggregator_error and outputs:
        lint = run.call_args_list[1].args[0]
        assert lint[:4] == ["lake", "env", "lean", "--run"], lint
        assert lint[4].endswith("scripts/lint_declarations.lean"), lint
        assert lint[5:] == ["MathlibExt.LintChanged", "MathlibExt.A", "MathlibExt.B"], lint
    return code, out.getvalue(), err.getvalue()


class MainTests(unittest.TestCase):
    def test_keeps_findings_on_added_declarations_only(self):
        code, out, _ = run_main([(1, OUTPUT)])
        self.assertEqual(code, 1)
        self.assertIn("::error file=MathlibExt/A.lean,line=9,col=1,title=docBlame::", out)
        self.assertIn("title=unusedArguments::1 unused argument:%0A", out)
        self.assertIn("::error file=MathlibExt/A.lean,line=11,title=simpNF::X.Pt.mk.injEq "
                      "LINTER FAILED", out)
        self.assertNotIn("line=3,", out)
        self.assertNotIn("B.lean", out)
        self.assertIn("3 on declarations the change adds, 4 on declarations it keeps, "
                      "1 in modules it does not change, 1 without a position", out)
        self.assertIn("not placed: simpNF: X.Gone.aux", out)

    def test_report_only_annotates_and_passes(self):
        code, out, _ = run_main([(1, OUTPUT)], extra=["--report-only"])
        self.assertEqual(code, 0)
        self.assertIn("::warning file=MathlibExt/A.lean,line=9,col=1,title=docBlame::", out)

    def test_passes_when_linting_passes(self):
        code, _, _ = run_main([(0, "-- Linting passed for MathlibExt.LintChanged.\n")])
        self.assertEqual(code, 0)

    def test_fails_when_the_files_do_not_build(self):
        self.assertEqual(run_main([], build_code=1, extra=["--report-only"])[0], 2)

    def test_fails_when_the_linters_do_not_finish(self):
        self.assertEqual(run_main([(1, "uncaught exception: unknown module\n")],
                                  extra=["--report-only"])[0], 2)

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        self.assertEqual(run_main([], aggregator_error=True)[0], 2)


if __name__ == "__main__":
    unittest.main()
