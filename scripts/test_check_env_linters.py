#!/usr/bin/env python3
"""Regressions for scripts/check_env_linters.py; never invokes Lean or Lake.

Run with: python3 -m unittest discover -s scripts -p test_check_env_linters.py
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

import check_env_linters as check
from check_env_linters import Finding
from lean_changes import ROOT, AggregatorError, ChangedFile, GitError

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

    def test_reads_a_module_name_with_a_space(self):
        output = ("/- The `simpNF` linter reports:\nSIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.\n"
                  "This linter can be disabled with `@[nolint simpNF]`. -/\n"
                  "-- MathlibExt.«My File»\n#check @X.Pt.mk.injEq /- LINTER FAILED:\nx -/\n")
        findings = check.parse_run_linter(output)
        self.assertEqual([(f.declaration, f.module) for f in findings],
                         [("X.Pt.mk.injEq", "MathlibExt.«My File»")])

    def test_declaration_names(self):
        self.assertEqual(check.declaration_name("@Foo.bar✝¹ 1 unused argument:"),
                         ("Foo.bar", "1 unused argument:", True))
        self.assertEqual(check.declaration_name("X.«weird name» definition missing"),
                         ("X.weird name", "definition missing", False))


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


HELPERS = """\
namespace ScopeProbe

def outer (x : Nat) : Nat := aux x 0
where
  aux (x y : Nat) : Nat := x
  /-- Doc. -/
  @[simp] bux : Nat :=
    let z := 1
    z

def pm : Nat → Nat
  | 0 => 1
  | n + 1 => go n
where go (n : Nat) : Nat := n

instance : Inhabited Nat where
  default := 0

def withField : Inhabited Nat where
  default := 3

def withRec (n : Nat) : Nat :=
  let rec loop : Nat → Nat
    | 0 => 0
    | k + 1 => loop k
  loop n

private def hidden (n : Nat) : Nat := go n where go (k : Nat) : Nat := k

end ScopeProbe
"""


# In a `module` file, a declaration is private unless it is marked `public` or is in a
# `public section` (and not marked `private`); scopes inside a public section are public too.
VISIBILITY = """\
module

namespace ReviewCases

def helper (y z : Nat) : Nat := y

/-- Moves to another file. -/
public def moved (y z : Nat) : Nat := y

structure Hidden where
  x : Nat

@[expose] public section

/-- Exposed. -/
def exposed (y z : Nat) : Nat := y

private def hiddenAgain (y z : Nat) : Nat := y

namespace Nested

/-- Inner. -/
def inner : Nat := 0

end Nested

section

/-- In a plain section inside the public one. -/
def plainInPublic : Nat := 0

end

end

def afterPublic : Nat := 0

theorem_wanted stillWanted : True

end ReviewCases
"""


DOTTED = """\
module

public section Outer.Inner

end Inner

/-- Still in the public section `Outer`. -/
def afterInner (y z : Nat) : Nat := y

end Outer

public section Shelf

section Level

end Shelf.Level

def afterBoth (y z : Nat) : Nat := y

namespace N.M

@[expose] public section

/-- Public. -/
def inside : Nat := 0

end

end M

def outside : Nat := 0

end N
"""


# In a `module` file, a helper is private unless its declaration exposes its body, a private
# field is private, and makes the constructor private; Lean's `#print` agrees on every name.
MODULE_CHILDREN = """\
module

public section

/-- Outer. -/
def outer (n : Nat) : Nat := aux n
where
  /-- Aux. -/
  aux (m : Nat) : Nat := m

/-- With rec. -/
def withRec (n : Nat) : Nat :=
  let rec loop (k : Nat) : Nat := k
  loop n

/-- Exposed. -/
@[expose] def exposedOuter (n : Nat) : Nat := eaux n
where
  eaux (m : Nat) : Nat := m

/-- An abbreviation exposes its body. -/
abbrev ab (n : Nat) : Nat := abAux n
where
  abAux (m : Nat) : Nat := m

/-- A structure. -/
structure S where
  /-- Public field. -/
  a : Nat
  private b : Nat

/-- No private field. -/
structure T where
  make ::
  /-- Public field. -/
  a : Nat

end

@[expose] public section

/-- In an exposed section. -/
def inExposed (n : Nat) : Nat := xaux n
where
  xaux (m : Nat) : Nat := m

/-- A theorem's helper is never exposed. -/
theorem thm (n : Nat) : n = n := h n
where
  h (k : Nat) : k = k := rfl

/-- Not exposed, in an exposed section. -/
@[no_expose] def hidden (n : Nat) : Nat := haux n
where
  haux (m : Nat) : Nat := m

end
"""


# A structure has one constructor: `mk` unless one is named, private if it is marked so; and an
# instance's helpers count as private, since one of a class of propositions keeps them private.
CONSTRUCTORS = """\
module

public section

/-- A named constructor. -/
structure Box where
  pack ::
  /-- The value. -/
  value : Nat

/-- A private named constructor. -/
structure Crate where
  private make ::
  /-- The value. -/
  value : Nat

/-- A class of propositions. -/
class P : Prop where
  out : True

instance instP : P := ⟨help⟩
where
  help : True := True.intro

end
"""


# `let rec` and `where` helpers, named after the helpers whose values hold them, as Lean's `#print`
# names each: a `let rec` in a `where` helper's value, in another `let rec`'s value (by indentation
# or inside brackets), after another one's `;`, in a structure-instance field's value, and in a
# helper after structure-instance fields.
LET_RECS = """\
namespace LR

def total (n : Nat) : Nat := go n
where
  go (k : Nat) : Nat :=
    let rec inner (j : Nat) : Nat := j
    inner k

def outer (n : Nat) : Nat :=
  let rec a (k : Nat) : Nat :=
    let rec b (j : Nat) : Nat := j
    b k
  a n

def flat (n : Nat) : Nat := let rec c (k : Nat) : Nat := k; let rec d (k : Nat) : Nat := k; c (d n)

def nest (n : Nat) : Nat := let rec e (k : Nat) : Nat := (let rec f (j : Nat) : Nat := j; f k); e n

/-- A structure. -/
structure Box where
  value : Nat

def boxed : Box where
  value := let rec g (k : Nat) : Nat := k; g 1

def boxed2 : Box where
  value := go2 1
where
  go2 (k : Nat) : Nat :=
    let rec inner2 (j : Nat) : Nat := j
    inner2 k

def pair (n : Nat) : Nat := let rec p (k : Nat) : Nat := k, q (j : Nat) : Nat := p j; q n

def props : Prop := let rec s : Prop := ∀ m : Nat, m = m; s

def typed (n : Nat) : Nat := let rec t : ∀ m : Nat, m = m := fun _ => rfl, u (k : Nat) := k; u n

def cons (n : Nat) : List Nat := let rec v : List Nat := [n], w (k : Nat) : List Nat := k :: v; w n

def pf (n : Nat) : Nat :=
  let rec @[reducible] a11 (k : Nat) : Nat :=
    let rec inner11 (j : Nat) : Nat := j
    inner11 k
  a11 n

def pa (n : Nat) : Nat := let rec a7 (k : Nat) : Nat := k, @[inline] b7 (j : Nat) := a7 j; b7 n

def pd (n : Nat) : Nat :=
  let rec
    /-- A documented one. -/
    @[reducible] a6 (k : Nat) : Nat := k
  a6 n

end LR
"""


class IndexTests(unittest.TestCase):
    def test_names_declarations_in_their_namespaces(self):
        index = check.index_source(SOURCE)
        self.assertEqual({line: sorted(names) for line, names in index.names_at.items()}, {
            13: ["MetaMathlibExt.foo"],
            15: ["MetaMathlibExt.bar"],
            17: ["MetaMathlibExt.instNamed"],
            19: ["instance in MetaMathlibExt: : Inhabited Bool"],
            23: ["MetaMathlibExt.Pt", "MetaMathlibExt.Pt.mk'"],
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

    def test_names_where_and_let_rec_helpers_but_not_structure_instance_fields(self):
        index = check.index_source(HELPERS)
        self.assertEqual({line: sorted(names) for line, names in index.names_at.items()}, {
            3: ["ScopeProbe.outer"],
            5: ["ScopeProbe.outer.aux"],
            7: ["ScopeProbe.outer.bux"],
            11: ["ScopeProbe.pm"],
            14: ["ScopeProbe.pm.go"],
            16: ["instance in ScopeProbe: : Inhabited Nat"],
            19: ["ScopeProbe.withField"],
            22: ["ScopeProbe.withRec"],
            23: ["ScopeProbe.withRec.loop"],
            28: ["ScopeProbe.hidden", "ScopeProbe.hidden.go"],
        })
        self.assertEqual(index.private_names, {"ScopeProbe.hidden", "ScopeProbe.hidden.go"})

    def test_keys_wanted_statements_apart_from_their_proofs(self):
        index = check.index_source(
            "module\n\nnamespace N\n\npublic theorem_wanted w (n : Nat) : n = n\n"
            "proof_wanted v : True\npublic def_wanted d : Nat\ninstance_wanted i : Inhabited Nat\n"
            "theorem t : True := trivial\n\nend N\n")
        self.assertEqual(index.names, {"wanted:N.w", "wanted:N.v", "wanted:N.d", "wanted:N.i",
                                       "N.t"})

    def test_module_files_make_declarations_private_outside_public_sections(self):
        index = check.index_source(VISIBILITY)
        self.assertEqual(index.private_names, {
            "ReviewCases.helper", "ReviewCases.hiddenAgain", "ReviewCases.Hidden",
            "ReviewCases.Hidden.mk", "ReviewCases.Hidden.x", "ReviewCases.afterPublic"})
        # A wanted statement is a placeholder, so it is pooled whatever its visibility.
        self.assertEqual(index.public_names, {
            "ReviewCases.moved", "ReviewCases.exposed", "ReviewCases.Nested.inner",
            "ReviewCases.plainInPublic", "wanted:ReviewCases.stillWanted"})
        # Outside a `module` file, only `private` makes a declaration private.
        plain = check.index_source(VISIBILITY.replace("module\n", "", 1))
        self.assertEqual(plain.private_names, {"ReviewCases.hiddenAgain"})

    def test_module_files_give_helpers_fields_and_constructors_their_own_visibility(self):
        index = check.index_source(MODULE_CHILDREN)
        self.assertEqual(index.private_names,
                         {"outer.aux", "withRec.loop", "S.b", "S.mk", "thm.h", "hidden.haux"})
        self.assertTrue({"outer", "withRec", "exposedOuter", "exposedOuter.eaux", "ab", "ab.abAux",
                         "S", "S.a", "T", "T.make", "T.a", "inExposed", "inExposed.xaux",
                         "thm"} <= index.public_names)
        # Elsewhere, helpers, fields and constructors follow their declaration, except a
        # private field.
        plain = check.index_source(MODULE_CHILDREN.replace("module\n", "", 1))
        self.assertEqual(plain.private_names, {"S.b"})

    def test_a_structure_has_one_constructor_with_its_own_visibility(self):
        index = check.index_source(CONSTRUCTORS)
        self.assertIn("Box.pack", index.public_names)
        self.assertNotIn("Box.mk", index.names)
        self.assertIn("Crate.make", index.private_names)
        self.assertNotIn("Crate.mk", index.names)
        self.assertIn("instP.help", index.private_names)

    def test_names_let_recs_after_the_helpers_that_hold_them(self):
        names = check.index_source(LET_RECS).names
        self.assertTrue({"LR.total.go", "LR.total.go.inner", "LR.outer.a", "LR.outer.a.b",
                         "LR.flat.c", "LR.flat.d", "LR.nest.e", "LR.nest.e.f",
                         "LR.boxed.g", "LR.boxed2.go2", "LR.boxed2.go2.inner2",
                         # `let rec p ... := v, q ... := w` declares both; a comma in a type or
                         # in a value that declares nothing after it does not.
                         "LR.pair.p", "LR.pair.q", "LR.props.s", "LR.typed.t", "LR.typed.u",
                         "LR.cons.v", "LR.cons.w",
                         # A declaration of a `let rec` may have a doc comment and attributes.
                         "LR.pf.a11", "LR.pf.a11.inner11", "LR.pa.a7", "LR.pa.b7",
                         "LR.pd.a6"} <= names)
        self.assertFalse({"LR.total.inner", "LR.outer.b", "LR.flat.c.d", "LR.nest.f",
                          "LR.boxed.value.g", "LR.boxed2.inner2", "LR.boxed2.value",
                          "LR.pair.p.q", "LR.props.m", "LR.props.s.m", "LR.typed.m",
                          "LR.cons.k", "LR.pf.inner11"} & names)

    def test_dotted_sections_open_and_close_one_scope_per_component(self):
        # `end Inner` closes only the inner of `section Outer.Inner`, so `Outer` stays public;
        # `end Shelf.Level` closes both `section Shelf` and `section Level`.
        index = check.index_source(DOTTED)
        self.assertIn("afterInner", index.public_names)
        self.assertIn("afterBoth", index.private_names)
        self.assertIn("N.M.inside", index.public_names)
        self.assertIn("N.outside", index.private_names)

    def test_unlexable_sources_fall_back_to_the_reported_line(self):
        index = check.index_source('def s := "unterminated\n')
        self.assertIsNone(index.code)
        self.assertEqual(index.declaration_line(1), 1)


def base_names(*public: str, **by_file: str) -> check.BaseNames:
    """Base declarations: public names of any changed file, and base texts by path at HEAD."""
    base = check.BaseNames(public=set(public))
    for path, text in by_file.items():
        base.add(check.index_source(text), path.replace("__", "/") + ".lean")
    return base


class PlaceTests(unittest.TestCase):
    def setUp(self):
        self.files = {file.path: file for file in FILES}
        self.indexes = {"MathlibExt/A.lean": check.index_source(HEAD_A),
                        "MathlibExt/B.lean": check.index_source(HEAD_B)}
        self.base = base_names("Y.old", MathlibExt__A=BASE_A)

    def place(self, finding: Finding, base=None):
        return check.place(finding, self.files, self.indexes,
                           self.base if base is None else base)

    def place_in(self, finding: Finding, head: dict[str, tuple[str, set[int]]],
                 base: check.BaseNames):
        """Place `finding` among the files of `head` (path: text and added lines)."""
        files = {path: ChangedFile(path, "M", frozenset(lines))
                 for path, (_, lines) in head.items()}
        indexes = {path: check.index_source(text) for path, (text, _) in head.items()}
        return check.place(finding, files, indexes, base)

    def test_a_finding_without_a_position_goes_to_the_module_that_lean_names(self):
        # `First.Second.lean` and `First/Second.lean` are two modules, which Lean names apart.
        text = "namespace X\n\nstructure Pt where\n  x : Nat\n\nend X\n"
        head = {"MathlibExt/First.Second.lean": (text, set(range(1, 7))),
                "MathlibExt/First/Second.lean": (text, set(range(1, 7)))}
        for module, path in (("MathlibExt.«First.Second»", "MathlibExt/First.Second.lean"),
                             ("MathlibExt.First.Second", "MathlibExt/First/Second.lean")):
            finding = Finding("X.Pt.mk.injEq", "simpNF", "", module)
            self.assertEqual(self.place_in(finding, head, base_names()).path, path)

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
                                base_names("X.keep"))
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
                                files, self.indexes, base_names("Y.old"))
        self.assertFalse(placement.added)
        placement = check.place(Finding("Y.old", "docBlame", "", "MathlibExt.B",
                                        "MathlibExt/B.lean", 10, 1),
                                files, self.indexes, base_names())
        self.assertTrue(placement.added)

    def test_an_edited_where_helper_is_not_added_and_a_new_one_is(self):
        base = "namespace ScopeProbe\n\ndef outer (x : Nat) : Nat := aux x 0\nwhere\n" \
               "  aux (x y : Nat) : Nat := x\n\nend ScopeProbe\n"
        head = base.replace(":= x\n", ":= x + 0\n  bux (x y : Nat) : Nat := x\n")
        files = {"MathlibExt/A.lean": (head, {5, 6})}
        old = Finding("ScopeProbe.outer.aux", "unusedArguments", "", "MathlibExt.A",
                      "MathlibExt/A.lean", 5, 1)
        self.assertFalse(self.place_in(old, files, base_names(MathlibExt__A=base)).added)
        new = Finding("ScopeProbe.outer.bux", "unusedArguments", "", "MathlibExt.A",
                      "MathlibExt/A.lean", 6, 1)
        self.assertTrue(self.place_in(new, files, base_names(MathlibExt__A=base)).added)

    def test_a_private_name_of_another_file_is_another_declaration(self):
        a = "namespace ScopeProbe\n\nprivate def helper (y : Nat) : Nat := y\n\n" \
            "def moved (y : Nat) : Nat := y\n\nend ScopeProbe\n"
        b = "namespace ScopeProbe\n\nprivate def helper (y z : Nat) : Nat := y\n\n" \
            "def moved (y : Nat) : Nat := y\n\nend ScopeProbe\n"
        base = base_names(MathlibExt__A=a, MathlibExt__B="namespace ScopeProbe\nend ScopeProbe\n")
        head = {"MathlibExt/A.lean": (a.replace("def moved (y : Nat) : Nat := y\n\n", ""), set()),
                "MathlibExt/B.lean": (b, {3, 4, 5, 6})}
        helper = Finding("ScopeProbe.helper", "unusedArguments", "", "MathlibExt.B",
                         "MathlibExt/B.lean", 3, 1, private=True)
        self.assertTrue(self.place_in(helper, head, base).added)
        # A public declaration that moves between the changed files is not new.
        moved = Finding("ScopeProbe.moved", "docBlame", "", "MathlibExt.B",
                        "MathlibExt/B.lean", 5, 1)
        self.assertFalse(self.place_in(moved, head, base).added)
        # In its own file, a private declaration is the same one.
        same = Finding("ScopeProbe.helper", "unusedArguments", "", "MathlibExt.A",
                       "MathlibExt/A.lean", 3, 1, private=True)
        head["MathlibExt/A.lean"] = (head["MathlibExt/A.lean"][0], {3})
        self.assertFalse(self.place_in(same, head, base).added)

    def test_a_proof_of_a_wanted_statement_is_a_new_declaration(self):
        wanted = ("module\n\nnamespace ScopeProbe\n\n/-- Wanted. -/\n"
                  "public theorem_wanted proved (n m : Nat) : n = n\n\n"
                  "/-- Still wanted. -/\npublic theorem_wanted later (n : Nat) : n = n\n\n"
                  "end ScopeProbe\n")
        proof = ("module\n\nnamespace ScopeProbe\n\n/-- Proved. -/\n"
                 "public theorem proved (n m : Nat) : n = n := rfl\n\nend ScopeProbe\n")
        base = base_names(WantedExt__Probe=wanted)
        # The pull request removes the wanted statement and proves it in another file.
        head = {"WantedExt/Probe.lean": (wanted.replace(
                    "/-- Wanted. -/\npublic theorem_wanted proved (n m : Nat) : n = n\n\n", ""),
                    set()),
                "MathlibExt/Proved.lean": (proof, set(range(1, 9)))}
        finding = Finding("ScopeProbe.proved", "unusedArguments", "1 unused argument:",
                          "MathlibExt.Proved", "MathlibExt/Proved.lean", 5, 1)
        self.assertTrue(self.place_in(finding, head, base).added)
        # Proving it in place reports the proof too.
        in_place = wanted.replace("public theorem_wanted proved (n m : Nat) : n = n",
                                  "public theorem proved (n m : Nat) : n = n := rfl")
        finding = Finding("ScopeProbe.proved", "unusedArguments", "1 unused argument:",
                          "WantedExt.Probe", "WantedExt/Probe.lean", 5, 1)
        self.assertTrue(self.place_in(finding, {"WantedExt/Probe.lean": (in_place, {6})},
                                      base).added)
        # A wanted statement that moves to another file is still the same one.
        moved = ("module\n\nnamespace ScopeProbe\n\n/-- Still wanted. -/\n"
                 "public theorem_wanted later (n : Nat) : n = n\n\nend ScopeProbe\n")
        head = {"WantedExt/Probe.lean": (wanted.replace(
                    "/-- Still wanted. -/\npublic theorem_wanted later (n : Nat) : n = n\n\n", ""),
                    set()),
                "WantedExt/Other.lean": (moved, set(range(1, 9)))}
        finding = Finding("ScopeProbe.later", "unusedArguments", "", "WantedExt.Other",
                          "WantedExt/Other.lean", 5, 1, private=True)
        self.assertFalse(self.place_in(finding, head, base).added)

    def test_a_module_private_declaration_does_not_hide_a_new_public_one(self):
        # File A declares `helper` with no visibility, so in a `module` file it is private; the
        # change adds a public `helper` of the same name to file B, and moves `moved` there.
        b_base = "module\n\nnamespace ReviewCases\n\nend ReviewCases\n"
        b_head = ("module\n\nnamespace ReviewCases\n\n"
                  "/-- New. -/\npublic def helper (y z : Nat) : Nat := y\n\n"
                  "/-- Moves to another file. -/\npublic def moved (y z : Nat) : Nat := y\n\n"
                  "end ReviewCases\n")
        a_head = VISIBILITY.replace(
            "/-- Moves to another file. -/\npublic def moved (y z : Nat) : Nat := y\n\n", "")
        base = base_names(MathlibExt__A=VISIBILITY, MathlibExt__B=b_base)
        # Every line of B's two declarations is added, so `moved` passes only by the move.
        head = {"MathlibExt/A.lean": (a_head, set()),
                "MathlibExt/B.lean": (b_head, set(range(5, 11)))}
        new = Finding("ReviewCases.helper", "unusedArguments", "", "MathlibExt.B",
                      "MathlibExt/B.lean", 5, 1)
        self.assertTrue(self.place_in(new, head, base).added)
        moved = Finding("ReviewCases.moved", "unusedArguments", "", "MathlibExt.B",
                        "MathlibExt/B.lean", 8, 1)
        self.assertFalse(self.place_in(moved, head, base).added)

    def test_dotted_sections_decide_what_a_move_or_a_new_declaration_is(self):
        # `afterInner` is public, so moving it to B is not new; `afterBoth` is private, so a new
        # public `afterBoth` in B is new.
        a_head = DOTTED.replace("/-- Still in the public section `Outer`. -/\n"
                                "def afterInner (y z : Nat) : Nat := y\n\n", "")
        b_head = ("module\n\n/-- Moved. -/\npublic def afterInner (y z : Nat) : Nat := y\n\n"
                  "/-- New. -/\npublic def afterBoth (y z : Nat) : Nat := y\n")
        base = base_names(MathlibExt__A=DOTTED, MathlibExt__B="module\n")
        head = {"MathlibExt/A.lean": (a_head, set()),
                "MathlibExt/B.lean": (b_head, set(range(1, 8)))}
        moved = Finding("afterInner", "unusedArguments", "", "MathlibExt.B", "MathlibExt/B.lean",
                        3, 1)
        self.assertFalse(self.place_in(moved, head, base).added)
        new = Finding("afterBoth", "unusedArguments", "", "MathlibExt.B", "MathlibExt/B.lean",
                      6, 1)
        self.assertTrue(self.place_in(new, head, base).added)

    def test_a_private_helper_does_not_hide_a_new_public_declaration(self):
        # In a `module` file, the helpers of public definitions are private, so new public
        # `outer.aux` and `withRec.loop` in another file are new.
        b_head = ("module\n\n/-- New. -/\npublic def outer.aux (y z : Nat) : Nat := y\n\n"
                  "/-- New. -/\npublic def withRec.loop (y z : Nat) : Nat := y\n")
        base = base_names(MathlibExt__A=MODULE_CHILDREN, MathlibExt__B="module\n")
        head = {"MathlibExt/A.lean": (MODULE_CHILDREN, set()),
                "MathlibExt/B.lean": (b_head, set(range(1, 8)))}
        for name, line in (("outer.aux", 3), ("withRec.loop", 6)):
            finding = Finding(name, "unusedArguments", "", "MathlibExt.B", "MathlibExt/B.lean",
                              line, 1)
            self.assertTrue(self.place_in(finding, head, base).added, name)

    def test_a_constructor_that_does_not_exist_hides_nothing(self):
        # `Box` names its constructor `pack`, so a new `Box.mk` in the same file is new.
        head = CONSTRUCTORS.replace("end\n", "/-- New. -/\ndef Box.mk (n unused : Nat) : Box := "
                                    "Box.pack n\n\nend\n")
        base = base_names(MathlibExt__A=CONSTRUCTORS)
        line = head.splitlines().index("/-- New. -/") + 1
        finding = Finding("Box.mk", "unusedArguments", "", "MathlibExt.A", "MathlibExt/A.lean",
                          line, 1)
        files = {"MathlibExt/A.lean": (head, {line, line + 1})}
        self.assertTrue(self.place_in(finding, files, base).added)

    def test_private_constructors_and_instance_helpers_hide_nothing_in_another_file(self):
        # `Crate.make` and `instP.help` are private in A, so public ones in B are new.
        b_head = ("module\n\n/-- New. -/\npublic def Crate.make (n unused : Nat) : Nat := n\n\n"
                  "/-- New. -/\npublic def instP.help (n unused : Nat) : Nat := n\n")
        base = base_names(MathlibExt__A=CONSTRUCTORS, MathlibExt__B="module\n")
        head = {"MathlibExt/A.lean": (CONSTRUCTORS, set()),
                "MathlibExt/B.lean": (b_head, set(range(1, 8)))}
        for name, line in (("Crate.make", 3), ("instP.help", 6)):
            finding = Finding(name, "unusedArguments", "", "MathlibExt.B", "MathlibExt/B.lean",
                              line, 1)
            self.assertTrue(self.place_in(finding, head, base).added, name)

    def test_a_let_rec_declaration_appended_after_a_comma_is_new(self):
        # The change appends `, q ...` to the line of an existing `let rec p`: `q` is new.
        base_text = ("namespace LR\n\ndef pair (n : Nat) : Nat := let rec p (k : Nat) : Nat := k; "
                     "p n\n\nend LR\n")
        head = base_text.replace("(k : Nat) : Nat := k; p n",
                                 "(k : Nat) : Nat := k, q (j spare : Nat) : Nat := p j; q n 0")
        files = {"MathlibExt/A.lean": (head, {3})}
        base = base_names(MathlibExt__A=base_text)
        new = Finding("LR.pair.q", "unusedArguments", "", "MathlibExt.A", "MathlibExt/A.lean", 3,
                      1)
        self.assertTrue(self.place_in(new, files, base).added)
        kept = Finding("LR.pair.p", "unusedArguments", "", "MathlibExt.A", "MathlibExt/A.lean", 3,
                       1)
        self.assertFalse(self.place_in(kept, files, base).added)
        # So is a `q` with an attribute.
        head = head.replace(", q (j spare", ", @[inline] q (j spare")
        files = {"MathlibExt/A.lean": (head, {3})}
        self.assertTrue(self.place_in(new, files, base).added)
        self.assertFalse(self.place_in(kept, files, base).added)

    def test_a_let_rec_in_a_helper_hides_no_declaration_of_the_parent(self):
        # `total.go.inner` is the `let rec` in `go`; a new `total.inner` is another declaration,
        # and an edit of the `let rec`'s line keeps `total.go.inner`.
        base_text = LET_RECS
        head = LET_RECS.replace("    let rec inner (j : Nat) : Nat := j",
                                "    let rec inner (j : Nat) : Nat := j + 0").replace(
            "end LR\n", "/-- New. -/\ndef total.inner (k spare : Nat) : Nat := k\n\nend LR\n")
        lines = head.splitlines()
        rec_line = lines.index("    let rec inner (j : Nat) : Nat := j + 0") + 1
        new_line = lines.index("def total.inner (k spare : Nat) : Nat := k") + 1
        base = base_names(MathlibExt__A=base_text)
        files = {"MathlibExt/A.lean": (head, {rec_line, new_line - 1, new_line})}
        new = Finding("LR.total.inner", "unusedArguments", "", "MathlibExt.A", "MathlibExt/A.lean",
                      new_line, 1)
        self.assertTrue(self.place_in(new, files, base).added)
        kept = Finding("LR.total.go.inner", "unusedArguments", "", "MathlibExt.A",
                       "MathlibExt/A.lean", rec_line, 5)
        self.assertFalse(self.place_in(kept, files, base).added)

    def test_a_new_helper_on_its_parent_s_line_is_new(self):
        # `retainedDef` stays; the change adds `where go` on its line, and `go` is new.
        base = base_names(MathlibExt__A="namespace R\n\ndef retainedDef (n : Nat) : Nat := n\n\n"
                                        "end R\n")
        head = ("namespace R\n\ndef retainedDef (n : Nat) : Nat := go n where go (k unused : "
                "Nat) : Nat := k\n\nend R\n")
        files = {"MathlibExt/A.lean": (head, {3})}
        helper = Finding("R.retainedDef.go", "unusedArguments", "", "MathlibExt.A",
                         "MathlibExt/A.lean", 3, 1)
        self.assertTrue(self.place_in(helper, files, base).added)
        parent = Finding("R.retainedDef", "unusedArguments", "", "MathlibExt.A",
                         "MathlibExt/A.lean", 3, 1)
        self.assertFalse(self.place_in(parent, files, base).added)

    def test_an_undecorated_wanted_statement_moved_between_module_files_is_kept(self):
        a_head = VISIBILITY.replace("theorem_wanted stillWanted : True\n\n", "")
        b_head = ("module\n\nnamespace ReviewCases\n\n"
                  "theorem_wanted stillWanted : True\n\nend ReviewCases\n")
        base = base_names(WantedExt__A=VISIBILITY)
        head = {"WantedExt/A.lean": (a_head, set()), "WantedExt/B.lean": (b_head, {1, 2, 3, 4, 5})}
        finding = Finding("ReviewCases.stillWanted", "unusedArguments", "", "WantedExt.B",
                          "WantedExt/B.lean", 5, 1, private=True)
        self.assertFalse(self.place_in(finding, head, base).added)

    def test_an_anonymous_instance_is_known_by_its_header(self):
        base = "namespace ScopeProbe\n\ninstance : Inhabited (Fin 3) := ⟨0⟩\n\nend ScopeProbe\n"
        head = base.replace("⟨0⟩", "⟨1⟩") + "instance : Inhabited (Fin 4) := ⟨0⟩\n"
        files = {"MathlibExt/A.lean": (head, {3, 6})}
        edited = Finding("ScopeProbe.instInhabitedFinOfNatNat", "synTaut", "", "MathlibExt.A",
                         "MathlibExt/A.lean", 3, 1)
        self.assertFalse(self.place_in(edited, files, base_names(MathlibExt__A=base)).added)
        new = Finding("instInhabitedFinOfNatNat", "synTaut", "", "MathlibExt.A",
                      "MathlibExt/A.lean", 6, 1)
        self.assertTrue(self.place_in(new, files, base_names(MathlibExt__A=base)).added)

    def test_a_finding_without_a_position_goes_to_its_enclosing_declaration(self):
        placement = self.place(Finding("X.Pt.mk.injEq", "simpNF", "LINTER FAILED", "MathlibExt.A"))
        self.assertEqual((placement.path, placement.line, placement.col, placement.added),
                         ("MathlibExt/A.lean", 11, None, True))
        placement = self.place(Finding("X.Pt.mk.injEq", "simpNF", "", "MathlibExt.A"),
                               base=base_names("X.Pt.mk"))
        self.assertFalse(placement.added)

    def test_findings_elsewhere_have_no_placement(self):
        self.assertIsNone(self.place(Finding("Z.Q.mk.injEq", "simpNF", "", "MathlibExt.Unchanged")))
        self.assertIsNone(self.place(Finding("X.Gone.aux", "simpNF", "", "MathlibExt.A")))
        self.assertIsNone(self.place(Finding("W.w", "docBlame", "", "MathlibExt.W",
                                             "MathlibExt/W.lean", 1, 1)))


@contextlib.contextmanager
def job_summary():
    """A job summary of the test's own, so that the fixtures' findings never reach the real one."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp, "summary.md")
        path.write_text("")
        with patch.dict("os.environ", {"GITHUB_ACTIONS": "true", "GITHUB_STEP_SUMMARY": str(path)}):
            yield path


def run_main(outputs: list[tuple[int, str]], files=FILES, build_code: int = 0, extra=(),
             aggregator_error=False, summary: list[str] | None = None) -> tuple[int, str, str]:
    """Run main() on fixture output; append the job summary it wrote to `summary`."""
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
    with job_summary() as summary_path, \
            patch.object(check, "changed_files", return_value=files), \
            patch.object(check, "deleted_files", return_value=[]), \
            patch.object(check, "base_text", side_effect=lambda base, path: bases.get(path)), \
            patch.object(check, "read_source", side_effect=lambda path: sources[path]), \
            patch.object(check, "aggregators", fake_aggregators), \
            patch.object(check.subprocess, "run", side_effect=results) as run, \
            patch.object(sys, "argv", ["check_env_linters.py", "--base", "HEAD^1", *extra]), \
            contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = check.main()
        if summary is not None:
            summary.append(summary_path.read_text())
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
        summary: list[str] = []
        code, out, _ = run_main([(1, OUTPUT)], extra=["--report-only"], summary=summary)
        self.assertEqual(code, 0)
        self.assertIn("| `docBlame` | 1 |", summary[0])
        self.assertIn("::warning file=MathlibExt/A.lean,line=9,col=1,title=docBlame::", out)

    def test_passes_when_linting_passes(self):
        summary: list[str] = []
        code, _, _ = run_main([(0, "-- Linting passed for MathlibExt.LintChanged.\n")],
                              summary=summary)
        self.assertEqual(code, 0)
        self.assertEqual(summary, [""])

    def test_an_unreadable_base_is_a_failure_to_run(self):
        out = io.StringIO()
        with patch.object(check, "changed_files", side_effect=GitError("no such ref: nope")), \
                patch.object(sys, "argv", ["check_env_linters.py", "--base", "nope"]), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(check.main(), 2)
        self.assertIn("no such ref: nope", out.getvalue())

    def test_fails_when_the_files_do_not_build(self):
        self.assertEqual(run_main([], build_code=1, extra=["--report-only"])[0], 2)

    def test_fails_when_the_linters_do_not_finish(self):
        self.assertEqual(run_main([(1, "uncaught exception: unknown module\n")],
                                  extra=["--report-only"])[0], 2)

    def test_an_existing_aggregator_name_is_a_failure_to_run(self):
        self.assertEqual(run_main([], aggregator_error=True)[0], 2)


if __name__ == "__main__":
    unittest.main()
