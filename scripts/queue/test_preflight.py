#!/usr/bin/env python3
"""Tests for scripts/queue/preflight.py. They need git and Python, not the network.

    python3 -m unittest discover -s scripts/queue -p 'test_*.py' -v
"""
from __future__ import annotations

import contextlib
import copy
import datetime as dt
import http.client
import io
import json
import os
import re
import shlex
import subprocess
import time
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import preflight  # noqa: E402

FIXTURES = HERE / "fixtures" / "preflight"
REPO = preflight.REPO
NOW = dt.datetime(2026, 11, 23, 18, 0, tzinfo=dt.timezone.utc)
REQUIRED = ("repository integrity", "build", "source-diagnostics", "guard")
# The workflow file behind each check, as on main; the fake repository's main defines the same jobs.
WORKFLOW_OF = {"repository integrity": ".github/workflows/ci.yml", "check the graph": ".github/workflows/ci.yml",
               "build": ".github/workflows/ci.yml", "guard": ".github/workflows/bump-guard.yml",
               "source-diagnostics": ".github/workflows/source-diagnostics.yml", "codex": ".github/workflows/codex.yml",
               "codex-verdict": ".github/workflows/codex.yml", "graph sync": ".github/workflows/graph-sync.yml",
               "public-references": ".github/workflows/public-references.yml"}
WORKFLOWS = {".github/workflows/ci.yml": "on: pull_request\njobs:\n  preflight:\n    name: repository integrity\n"
                                         "  graph:\n    name: check the graph\n  build:\n    runs-on: x\n",
             ".github/workflows/bump-guard.yml": "on: pull_request\njobs:\n  guard:\n    runs-on: x\n",
             ".github/workflows/source-diagnostics.yml": "on: pull_request\njobs:\n  source-diagnostics:\n    runs-on: x\n"}


def load(name: str):
    return json.loads((FIXTURES / name).read_text())


class FakeGitHub:
    """Answers preflight's GitHub reads from dictionaries, and records the calls."""

    def __init__(self, responses: dict, logs: dict | None = None, queue: dict | None = None):
        self.repo = REPO
        self.responses = responses
        self.logs = logs or {}
        self.queue = queue or queue_answer([])
        self.calls: list[str] = []
        self.mutations: list[dict] = []
        self.mutation_error: Exception | None = None
        self.mutation_answer: dict | None = None
        self.queued_after: dict | None = None

    def get(self, path: str):
        self.calls.append(path)
        if path not in self.responses:
            raise preflight.Failure(f"GET {path}: HTTP 404")
        return copy.deepcopy(self.responses[path])

    def paged(self, path: str, key: str | None = None, max_pages: int = 10) -> list:
        data = self.get(path)
        return data[key] if key else data

    def graphql(self, query: str, variables: dict, attempts: int = 3) -> dict:
        if "byteSize" in query:  # blob sizes, before downloading: small unless a test says otherwise
            sizes = getattr(self, "blob_sizes", {})
            return {"data": {"repository": {alias: {"byteSize": sizes.get(oid, 100)} for alias, oid in
                                            re.findall(r'(b\d+): object\(oid: "([0-9a-f]{40})"\)', query)}}}
        if "enqueuePullRequest" in query:
            self.mutations.append(dict(variables, attempts=attempts))
            if self.mutation_error:
                raise self.mutation_error
            return self.mutation_answer or {"data": {"enqueuePullRequest": {"mergeQueueEntry": {"position": 4, "state": "QUEUED"}}}}
        if self.mutations and self.queued_after:
            return copy.deepcopy(self.queued_after)
        return copy.deepcopy(self.queue)

    def read_log(self, job_id: int, pattern: re.Pattern, max_bytes: int = 0):
        if job_id not in self.logs:
            raise preflight.Failure(f"GET job {job_id} logs: HTTP 404")
        return pattern.search(self.logs[job_id])


def queue_answer(entries: list[tuple[int, str]], own: dict | None = None, more: bool = False,
                 main: str = "4" * 40) -> dict:
    nodes = [{"position": i + 1, "state": "AWAITING_CHECKS", "enqueuedAt": "2026-11-23T17:00:00Z",
              "pullRequest": {"number": n, "headRefOid": sha}} for i, (n, sha) in enumerate(entries)]
    return {"data": {"repository": {"ref": {"target": {"oid": main}}, "pullRequest": {"mergeQueueEntry": own},
                                    "mergeQueue": {"entries": {"totalCount": len(nodes), "nodes": nodes,
                                                               "pageInfo": {"hasNextPage": more, "endCursor": "c"}}}}}}


def github_6650(head: str | None = None) -> tuple[dict, dict]:
    """The API responses and job logs of #6650, as read on 23 November 2026, optionally for another head."""
    fixture = load("github_6650.json")
    real = fixture["pulls/6650"]["head"]["sha"]
    head = head or real
    swap = lambda value: json.loads(json.dumps(value).replace(real, head))  # noqa: E731
    responses = {
        f"/repos/{REPO}/pulls/6650": swap(fixture["pulls/6650"]),
        f"/repos/{REPO}/pulls/6650/reviews": swap(fixture["reviews"]),
        f"/repos/{REPO}/commits/{head}/check-runs": swap(fixture["check_runs"]),
        f"/repos/{REPO}/rules/branches/main": fixture["rules"],
        f"/repos/{REPO}/actions/runs/{fixture['run_id']}": swap(fixture["run"]),
        f"/repos/{REPO}/actions/runs/{fixture['codex_verdict_run']['id']}": fixture["codex_verdict_run"],
    }
    responses[f"/repos/{REPO}/actions/jobs/{fixture['job_id']}"] = {"run_id": fixture["run_id"], "name": "build"}
    responses[f"/repos/{REPO}/actions/jobs/{fixture['codex_verdict_job_id']}"] = {
        "run_id": fixture["codex_verdict_run"]["id"], "name": "codex-verdict"}
    # The workflow runs behind the check runs: pull_request runs that GitHub lists with #6650 and main.
    mine = [{"number": 6650, "base": {"ref": "main"}}]
    for check in fixture["check_runs"]["check_runs"]:
        run_id = re.search(r"/actions/runs/(\d+)/", check.get("details_url") or "")
        if run_id:
            run = responses.setdefault(f"/repos/{REPO}/actions/runs/{run_id.group(1)}",
                                       {"id": int(run_id.group(1)), "event": "pull_request", "head_sha": head})
            run.setdefault("pull_requests", mine)
            run.setdefault("path", WORKFLOW_OF.get(check["name"], ".github/workflows/other.yml"))
            run.setdefault("created_at", check.get("started_at") or "2026-11-23T16:00:00Z")
    logs = {fixture["job_id"]: (FIXTURES / "checkout_log_6650.txt").read_text().replace(real, head),
            fixture["codex_verdict_job_id"]: (FIXTURES / "codex_verdict_log_6650.txt").read_text()}
    return responses, logs


# --------------------------------------------------------------------------------------------------


class DeclarationTests(unittest.TestCase):
    def names(self, text: str, auxiliary: bool = False, local: bool = False, eqns: bool = False) -> list[str]:
        """The names declarations() reads, without the members Lean adds to every inductive type and
        constructor unless `auxiliary` is set (test_auxiliary_names covers those)."""
        suffixes = tuple(f".{aux}" for aux in preflight._AUXILIARY + preflight._CONSTRUCTOR_AUXILIARY)
        return [name.split("#", 1)[0] for name, _ in preflight.declarations(text)  # markers without fingerprints
                if (auxiliary or not name.endswith(suffixes)) and (local or not name.startswith("?local:"))
                and (eqns or not name.startswith(("?eqns:", "?toproj:")))]

    def test_auxiliary_names(self):
        text = "namespace N\ninductive S where | a\n@[to_additive AddT] structure T where\n  x : Nat\nend N\n"
        aux = [f"N.S.{a}" for a in preflight._AUXILIARY]
        self.assertEqual(self.names(text, auxiliary=True), [
            "N.S", *aux, "N.S.a", "N.S.a.inj", "N.S.a.injEq", "N.S.a.sizeOf_spec", "N.T", "N.AddT",
            *[a.replace(".S.", ".T.") for a in aux], "?gen:to_additive:N.T", "N.T.x", "N.T.mk", "N.T.mk.inj",
            "N.T.mk.injEq", "N.T.mk.sizeOf_spec"])

    def test_namespaces_sections_and_end(self):
        text = """
namespace A.B
def one : Nat := 1
section S
theorem two : True := trivial
end S
namespace C
lemma three : True := trivial
end C
noncomputable section
abbrev four := 4
end
end A.B
def five := 5
"""
        self.assertEqual(self.names(text), ["A.B.one", "A.B.two", "A.B.C.three", "A.B.four", "five"])

    def test_modifiers_attributes_and_skipped_forms(self):
        text = """
namespace N
@[simp, to_additive (attr := simp) "doc [x]"] theorem attr_one : True := trivial
@[simp]
protected noncomputable def two : Nat := 2
private def hidden : Nat := 0
instance : Inhabited Nat := ⟨0⟩
instance (priority := 100) namedInst : Inhabited Nat := ⟨0⟩
open Classical in theorem opened : True := trivial
def _root_.Top.level : Nat := 3
def Sub.dotted : Nat := 4
def «weird name» : Nat := 5
def withUniverses.{u} : Nat := 6
alias aliased := two
alias ⟨mp, mpr⟩ := Iff.rfl
alias ⟨_, onlyBackward⟩ := Iff.rfl
alias ⟨splitForward,
  splitBackward⟩ := Iff.rfl
example : True := trivial
public theorem_wanted wanted_one : True
class inductive Shape | circle
structure Point where
  x : Nat
end N
"""
        self.assertEqual(self.names(text), [
            "N.attr_one", "?gen:to_additive:N.attr_one", "N.two", "N.instInhabitedNat", "?inst:N:Inhabited",
            "N.namedInst", "N.opened", "Top.level", "N.Sub.dotted", "N.«weird name»",
            "N.withUniverses", "N.aliased", "N.mp", "N.mpr", "N.onlyBackward", "N.splitForward",
            "N.splitBackward", "N.Shape", "N.Shape.circle", "N.Point", "N.Point.x", "N.Point.mk"])
        self.assertIn("?local:N.wanted_one", self.names(text, local=True))  # a private placeholder

    def test_comments_strings_and_mutual(self):
        text = """
/- a block comment
   def commented : Nat := 0
   /- nested -/ still a comment
-/
/-- A docstring that says def nope. -/
def real : String := "-- not a comment /- nor this"
-- def lineComment : Nat := 0
namespace M
mutual
def even : Nat → Bool := fun _ => true
def odd : Nat → Bool := fun _ => false
end
def after : Nat := 1
def text : String := "first
end M
theorem ghost : True := trivial
last"
end M
"""
        self.assertEqual(self.names(text), ["real", "M.even", "M.odd", "M.after", "M.text"])
        self.assertEqual(dict(preflight.declarations(text))["real"], 7)

    def test_module_visibility(self):
        text = """/- header -/
module

public import Mathlib.Logic.Basic

namespace Hidden
def privateByDefault := 1
public def exported := 2
end Hidden

@[expose] public noncomputable section
namespace Shown
def visible := 3
private
def hiddenAgain := 4
section
def nested := 5
end
end Shown
end
"""
        self.assertEqual(self.names(text), ["Hidden.exported", "Shown.visible", "Shown.nested"])
        scoped = "module\npublic namespace N\ndef x := 1\nend N\npublic mutual\ndef y := 2\nend\nnamespace M\ndef z := 3\nend M\n"
        self.assertEqual(self.names(scoped), ["N.x", "y"])

    def test_declarations_split_over_lines(self):
        text = """
namespace N
@[simp,
  inline] def afterLongAttribute := 1
public theorem
    nameOnNextLine : True := trivial
instance
    : Inhabited Nat := ⟨0⟩
end N
"""
        self.assertEqual(self.names(text), ["N.afterLongAttribute", "N.nameOnNextLine", "N.instInhabitedNat",
                                            "?inst:N:Inhabited"])

    def test_generated_names(self):
        text = """
namespace N
@[to_additive addFoo] theorem mulFoo : True := trivial
@[to_additive (attr := simp) addBar "doc"]
theorem mulBar : True := trivial
@[to_additive existing] theorem mulBaz : True := trivial
@[simps] def equiv : Nat ≃ Nat := Equiv.refl _
@[reassoc (attr := simp)] theorem comp_id : True := trivial
@[ext] structure Pt where
  x : Nat
instance : Fintype (Fin n → ℕ) := sorry
instance {α : Type} [Inhabited α] : Inhabited (Box α) := ⟨⟨default⟩⟩
end N
"""
        self.assertEqual(self.names(text), [
            "N.mulFoo", "N.addFoo", "N.mulBar", "N.addBar", "N.mulBaz", "N.equiv", "?gen:simps:N.equiv",
            "N.comp_id", "N.comp_id_assoc", "N.Pt",
            "N.Pt.ext", "N.Pt.ext_iff", "N.Pt.x", "N.Pt.mk", "N.instFintypeFinNat", "?inst:N:Fintype", "N.instInhabitedBox",
            "?inst:N:Inhabited"])

    def test_structure_and_inductive_names(self):
        text = """
namespace N
structure S where
  x : Nat
  y z : Nat := 0
  private secret : Nat
  protected w : Nat
structure T extends S, Other.U where
  mk' ::
  (a : Nat)
class C (α : Type) where
  op : α → α
inductive I
  | zero
  | succ (n : I) : I
inductive J | a | b
theorem after : True := trivial
private structure P where
  hidden : Nat
section
  structure Q where
    q : Nat
  theorem indented : True := trivial
end
end N
"""
        self.assertEqual(self.names(text), [
            "N.S", "N.S.x", "N.S.y", "N.S.z", "N.S.w", "N.S.mk", "N.T", "N.T.toS", "N.T.toU", "N.T.mk'", "N.T.a",
            "N.C", "N.C.op", "N.C.mk", "N.I", "N.I.zero", "N.I.succ", "N.J", "N.J.a", "N.J.b", "N.after",
            "N.Q", "N.Q.q", "N.Q.mk", "N.indented"])

    def test_structure_field_forms(self):
        text = """
namespace N
structure S where
  apply (n : Nat) : Nat
  pairwise :
    Pairwise fun i j : Fin 2 => i ≠ j
  restriction (U V : Nat)
      (h : U ≤ V) : Nat
structure M {X Y : Type}
    (f : X → Y)
    extends Base f, Other where
  field : Nat
structure Weird where
  ??? bad line
end N
"""
        self.assertEqual(self.names(text), [
            "N.S", "N.S.apply", "N.S.pairwise", "N.S.restriction", "N.S.mk", "N.M", "N.M.toBase", "N.M.toOther",
            "N.M.field", "N.M.mk", "N.Weird", "?gen:structure:N.Weird", "N.Weird.mk"])
        self.assertIsNone(preflight._field_names("Pairwise fun i j : Fin n => Disjoint"))

    def test_derived_instances(self):
        text = """
namespace N
structure S where
  x : Nat
deriving DecidableEq, Repr
inductive I
  | a | b
  deriving Ord
inductive J | c | d deriving Hashable
structure T extends S
  deriving BEq
deriving instance DecidableEq for Var, Tm
end N
"""
        self.assertEqual(self.names(text), [
            "N.S", "N.S.x", "N.S.mk", "N.instDecidableEqS", "N.instReprS", "N.I", "N.I.a", "N.I.b", "N.instOrdI",
            "N.J", "N.J.c", "N.J.d", "N.instHashableJ", "N.T", "N.instBEqT", "N.T.toS", "N.T.mk",
            "N.instDecidableEqVar", "N.instDecidableEqTm"])

    def test_deriving_over_several_lines(self):
        text = """
namespace N
deriving instance DecidableEq for
  Var
deriving noncomputable instance Repr, BEq for Var,
  Tm
structure S where
  x : Nat
deriving DecidableEq,
  Repr
inductive I
  | a
  deriving Ord,
    Hashable
deriving instance DecidableEq for (Foo α)
end N
"""
        self.assertEqual(self.names(text), [
            "N.instDecidableEqVar", "N.instReprVar", "N.instBEqVar", "N.instReprTm", "N.instBEqTm", "N.S", "N.S.x",
            "N.S.mk", "N.instDecidableEqS", "N.instReprS", "N.I", "N.I.a", "N.instOrdI", "N.instHashableI",
            "?gen:deriving:N.instance"])

    def test_attached_deriving_over_several_lines(self):
        text = """
namespace N
inductive K
  | a
  deriving
    DecidableEq
inductive L | b deriving Repr,
  DecidableEq
structure S where
  x : Nat
deriving
  BEq
theorem t : True := trivial
inductive M
  | c
  deriving
theorem u : True := trivial
structure P where
  y : Nat
deriving
theorem v : True := trivial
end N
"""
        self.assertEqual(self.names(text), [
            "N.K", "N.K.a", "N.instDecidableEqK", "N.L", "N.L.b", "N.instReprL", "N.instDecidableEqL", "N.S", "N.S.x",
            "N.S.mk", "N.instBEqS", "N.t", "N.M", "N.M.c", "?gen:deriving:N.M", "N.u", "N.P", "N.P.y", "N.P.mk",
            "?gen:deriving:N.instance", "N.v"])

    def test_deriving_with_attributes(self):
        text = """
namespace N
inductive K | a deriving @[expose] DecidableEq
structure S where
  x : Nat
deriving @[expose] Repr, (Weird)
deriving instance @[expose] BEq for Var
end N
"""
        self.assertEqual(self.names(text), ["N.K", "N.K.a", "N.instDecidableEqK", "N.S", "N.S.x", "N.S.mk", "N.instReprS",
                                            "?gen:deriving:N.S", "N.instBEqVar"])

    def test_markers_change_with_their_declaration(self):
        base = "namespace N\n@[simps apply] def e : Nat ≃ Nat := Equiv.refl _ -- note\ndef other := 1\nend N\n"
        markers = lambda text: [n for n, _ in preflight.declarations(text) if n.startswith("?gen:")]  # noqa: E731
        self.assertEqual(markers(base.replace("other := 1", "other := 2")), markers(base))  # another declaration
        self.assertEqual(markers("-- a comment\n" + base), markers(base))
        self.assertEqual(markers(base.replace("-- note", "-- a much longer note")), markers(base))
        self.assertNotEqual(markers(base.replace("simps apply", "simps apply symm_apply")), markers(base))
        above = base.replace("@[simps apply] def", "@[simps apply]\ndef")  # the attribute on the line above
        self.assertNotEqual(markers(above.replace("simps apply", "simps apply symm_apply")), markers(above))
        last = "namespace N\n@[simps apply] def e : Nat ≃ Nat :=\n  Equiv.refl _\nend N\n"
        appended = last.replace("end N", "theorem t : True := trivial\nend N")
        self.assertEqual(markers(appended), markers(last))  # appending another declaration after it
        changes = [("a", "b", "MathlibExt/E.lean")]
        texts = {"a": base, "b": base.replace("simps apply", "simps apply symm_apply")}
        self.assertEqual([n.split("#")[0] for n in preflight.placed_declarations(changes, texts) if n.startswith("?")],
                         ["?gen:simps:N.e"])

    def test_declarations_after_scoped_commands(self):
        text = """
namespace N
attribute [local instance] Classical.propDecidable in theorem dup : True := trivial
local notation "x" => 1 in theorem e : True := trivial
open A in attribute [simp] b in @[simp] theorem c : True := trivial
attribute [simp] foo
local instance inst : Inhabited Nat := ⟨0⟩
open Classical in
theorem f : True := trivial
end N
"""
        self.assertEqual(self.names(text), ["N.dup", "N.e", "N.c", "N.inst", "N.f"])

    def test_initializers_and_syntax(self):
        text = """
namespace N
initialize cache : IO.Ref Nat ← IO.mkRef 0
initialize do pure ()
syntax (name := foo) "foo" : term
notation "‖" x "‖" => x
local notation "x" => 1
scoped infix:50 " ~ " => Eq
macro_rules | `(foo) => `(1)
end N
"""
        self.assertEqual(self.names(text), ["N.cache", "N.foo", "?parser:N.«term‖_‖»", "?parser:N.«term_~_»", "?gen:command:N.macro_rules"])  # a rule may make commands
        module = "module\nnamespace N\ndeclare_syntax_cat step\nend N\n"  # public, outside any public section
        self.assertEqual(self.names(module), ["Lean.Parser.Category.step"])
        syntax = 'module\nnamespace N\nsyntax (name := probe) "a" : term\nlocal syntax (name := mine) "b" : term\nend N\n'
        self.assertEqual(self.names(syntax), ["N.probe"])  # exported unless local, outside a public section too
        split = "namespace N\ninitialize\n  cache : IO.Ref Nat ← IO.mkRef 0\ninitialize\n  pure ()\nend N\n"
        self.assertEqual(self.names(split), ["N.cache"])
        literal = "namespace N\nsyntax \"foo\" : term\nend N\n"  # Lean names the parser after its literal
        self.assertNotEqual(preflight.declarations(literal), preflight.declarations(literal.replace("foo", "bar")))

    def test_where_helpers_and_let_rec(self):
        text = ("namespace B\npublic def contains (x : Nat) : List Nat → Bool\n  | _ => containsList x []\nwhere\n"
                "  containsList (x : Nat) : List Nat → Bool\n    | [] => false\n  @[simp] other : Nat := 1\n"
                "termination_by t => t\ninstance : Foo where\n  bar := 1\ndef f := go 1\nwhere go (n : Nat) : Nat := n\n"
                "def g : Nat :=\n  let rec loop (n : Nat) : Nat := n\n  loop 1\ntheorem after : True := trivial\nend B\n")
        self.assertEqual(self.names(text), ["B.contains", "B.contains.containsList", "B.contains.other", "B.instFoo",
                                            "?inst:B:Foo", "B.f", "B.f.go", "B.g", "B.g.loop", "B.after"])
        same_line = ("namespace N\ndef f : Nat := go where\n  go : Nat := 1\ndef g : Nat := let rec loop : Nat := 1; loop\n"
                     "def h := k where k := 2\ntheorem t : True := trivial\nend N\n")
        self.assertEqual(self.names(same_line), ["N.f", "N.f.go", "N.g", "N.g.loop", "N.h", "N.h.k", "N.t"])
        nested = ("namespace N\ndef f := g 1\nwhere\n  g (n : Nat) : Nat := h n\n  where\n    h (m : Nat) : Nat := m\n"
                  "  k : Nat := 2\ndef f2 := g 1\nwhere\n  g (n : Nat) : Nat := h n where\n"
                  "    h (m : Nat) : Nat := let rec q : Nat := 1; q\nend N\n")
        self.assertEqual(self.names(nested), ["N.f", "N.f.g", "N.f.g.h", "N.f.k", "N.f2", "N.f2.g", "N.f2.g.h", "N.f2.g.h.q"])

    def test_commands_it_does_not_know(self):
        text = ("namespace N\nmy_macro foo\nregister_grind_attr multiset\n#print axioms foo\nadd_decl_doc foo\n"
                "theorem t : True :=\ntrivial\nprivate def p : Nat := 1\ntermination_by 1\nu = v\nend N\n")
        self.assertEqual(self.names(text), ["?gen:command:N.my_macro", "?gen:command:N.register_grind_attr", "N.t"])
        after_def = "namespace N\ndef preceding : Nat := 0\nemit_helper dup\nproof_wanted wanted : True\nend N\n"
        self.assertEqual(self.names(after_def, local=True), ["N.preceding", "?gen:command:N.emit_helper", "?local:N.wanted"])
        forms = ("namespace N\n  my_macro a\npublic my_macro b\n@[simp] my_macro c\nopen Foo in my_macro d\n"
                 "theorem t : True := by\n  simp_all\nvariable (x : Nat)\n  (y : Nat)\nattribute [simp]\n  foo bar\n"
                 "public instance_wanted instFoo : Foo\nend N\n")
        self.assertEqual(self.names(forms), ["?gen:command:N.my_macro"] * 4 + ["N.t"])  # continuations aside
        siblings = "namespace N\n  def preceding : Nat := 0\n  emit_helper dup\n  emit_helper dup2\nend N\n"
        self.assertEqual(self.names(siblings), ["N.preceding", "?gen:command:N.emit_helper", "?gen:command:N.emit_helper"])
        local = "namespace N\nprivate def hidden := 1\ninstance_wanted instLocal : Inhabited Nat\nend N\n"
        self.assertEqual(self.names(local, local=True), ["?local:N.hidden", "?local:N.instLocal"])  # module-local
        hashed = ("namespace N\n#emit_def dup\n#print axioms foo\n#guard_msgs in theorem g : True := trivial\n"
                  "theorem t : True := by\n  #check 1\n  trivial\nend N\n")
        self.assertEqual(self.names(hashed), ["?gen:command:N.emit_def", "N.g", "N.t"])  # `#print` and `#check` aside
        for custom in ("EmitDef duplicateName", "emit2 dup", "EmitDef! dup", "Foo.bar x", "«my cmd» x"):  # any form
            self.assertEqual(self.names(f"namespace N\n{custom}\nend N\n")[0][:len("?gen:command:N.")], "?gen:command:N.", custom)
        self.assertEqual(self.names("theorem foo :\nNat.succ 0 = 1 := rfl\n"), ["foo"])  # a line left open goes on
        self.assertEqual(self.names("namespace N\nopen Nat in\nemit_named dup\nend N\n"), ["?gen:command:N.emit_named"])  # a command follows
        self.assertEqual(self.names("namespace N\nopen Nat in\n  emit_named dup\nend N\n"), ["?gen:command:N.emit_named"])  # indented too
        self.assertEqual(self.names("namespace N\nopen Nat in\n§ dup\nend N\n"), ["?gen:command:N.command"])  # any first character
        deriving = "namespace N\nstructure Earlier where\n  z : Nat\nprivate structure A where\n  x : Nat\nderiving Inhabited\nend N\n"
        self.assertIn("?maybe:N.instInhabitedA", self.names(deriving))  # the clause belongs to the private A
        self.assertNotIn("N.instInhabitedEarlier", self.names(deriving))
        rules = "namespace N\nmacro_rules\n| `(emit_dup) => `(def {name} := 1)\nend N\n"
        marker = lambda text: [n for n, _ in preflight.declarations(text) if n.startswith("?gen:command")]
        self.assertNotEqual(marker(rules.format(name="previous")), marker(rules.format(name="dup")))  # its alternatives count
        elab = "@[command_elab {key}] def serve : CommandElab := fun _ => pure ()\n"
        self.assertNotEqual(marker(elab.format(key="emitAlpha")), marker(elab.format(key="emitBeta")))  # its registration counts
        self.assertEqual(self.names("namespace N\nλemit dup\nend N\n"), ["?gen:command:N.λemit"])  # a letter of any script
        self.assertIn("?gen:command:N.elab_rules", self.names("namespace N\nelab_rules : command\n  | `(emit_dup) => pure ()\nend N\n"))
        self.assertEqual(self.names("namespace A.B\ndef x := 1\nend B\ndef y := 2\nend A\ndef z := 3\n"), ["A.B.x", "A.y", "z"])
        self.assertEqual(self.names("namespace Set\nnamespace HasDensity\ndef x := 1\nend Set.HasDensity\ndef z := 1\n"),
                         ["Set.HasDensity.x", "z"])  # `end A.B` closes both
        self.assertIn("N.S.x", self.names("namespace N\nstructure S (α : Type)\nwhere\n  x : α\nend N\n"))  # `where` below
        self.assertIn("N.I.a", self.names("namespace N\ninductive I (α : Type)\nwhere\n  | a : α → I α\nend N\n"))
        self.assertIn("N.I.a", self.names("namespace N\ninductive I\n  | @[simp] a\n  | b\nend N\n"))  # an attributed constructor
        additive = self.names("namespace N\n@[to_additive (attr := reassoc) addFoo] theorem mulFoo : True := trivial\nend N\n", auxiliary=True)
        self.assertIn("N.addFoo_assoc", additive)  # the additive copy's generated name
        self.assertIn("?gen:simps:N.addEquiv",
                      self.names("namespace N\n@[to_additive (attr := simps) addEquiv] def mulEquiv : Nat := 0\nend N\n"))
        self.assertEqual(self.names("def c : Char := '\\\"'\ndef after := 1\n"), ["c", "after"])  # the literal '\"'
        self.assertIn("S", self.names("attribute [local instance] bar in\n  public structure S where\n  x : Nat\n"))
        self.assertIn("?gen:command:N.macro", self.names("namespace N\nmacro \"emit\" x:ident : command => `(def $x := 1)\nend N\n", auxiliary=True))
        self.assertNotIn("?gen:command:N.macro", self.names("namespace N\nmacro \"twice\" x:term : term => `($x + $x)\nend N\n"))
        aux = ("rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ctorIdx", "_impl")
        derived = [n for n in self.names("namespace N\nprivate inductive T | a | b deriving DecidableEq\nend N\n", local=True)]
        self.assertIn("?maybe:N.instDecidableEqT", derived)  # a local type's instances may be public
        self.assertIn("?maybe:N.instInhabitedA", self.names("namespace N\nprivate structure A where\n  x : Nat\n  deriving Inhabited\nend N\n"))
        self.assertIn("?gen:structure:N.S", self.names("namespace N\nstructure S extends (id Parent) where\nend N\n"))  # a term
        self.assertIn("?toproj:N.S", self.names("namespace N\nstructure S extends Alias where\nend N\n", eqns=True))  # maybe an alias
        bare = "namespace N\nemit_fixed\ntheorem t : True :=\ntrivial\nend N\n"
        self.assertEqual(self.names(bare), ["?gen:command:N.emit_fixed", "N.t"])  # a bare word may be a command
        tactics = ("theorem t : True := by\n  have h : True := by\n    rw [x]\n    module\n  have k : True := by\n"
                   "    rw [y]\n    simp\n  open Classical in\n  exact trivial\n")
        self.assertEqual(self.names(tactics), ["t"])  # a tactic named like a command does not end the proof
        self.assertEqual(preflight._let_recs("  let rec @[reducible] go (n : Nat) :"), ["go"])

    def test_attribute_commands_that_generate_names(self):
        text = ("namespace A.B\nopen Foo\nattribute [reassoc] Hom.j_comp\nattribute [instance] Shtuka.mono_j\n"
                "attribute [simps] Q.e\nattribute [to_additive bar] baz\nattribute [reassoc] _root_.r\nend A.B\n")
        self.assertEqual(self.names(text), [  # where a relative target resolves is open: possible names only
            "?maybe:A.B.Hom.j_comp_assoc", "?maybe:A.Hom.j_comp_assoc", "?maybe:Hom.j_comp_assoc",
            "?maybe:A.B.Foo.Hom.j_comp_assoc", "?maybe:A.Foo.Hom.j_comp_assoc", "?maybe:Foo.Hom.j_comp_assoc",
            "?gen:simps:A.B.Q.e", "?gen:simps:A.Q.e", "?gen:simps:Q.e", "?gen:simps:A.B.Foo.Q.e", "?gen:simps:A.Foo.Q.e",
            "?gen:simps:Foo.Q.e", "?maybe:A.B.bar", "r_assoc"])
        over_lines = "attribute [reassoc]\n  _root_.Outer.Inner.foo «two words»\ntheorem t : True := trivial\n"
        self.assertEqual(self.names(over_lines), ["Outer.Inner.foo_assoc", "«two words_assoc»", "t"])
        opened = "namespace Outer\nopen Inner\nattribute [reassoc] foo\nend Outer\n"
        self.assertIn("?maybe:Outer.Inner.foo_assoc", self.names(opened))  # a relative open, read in Outer
        declared = "namespace N\ntheorem foo : True := trivial\nattribute [reassoc] foo\nend N\n"
        self.assertEqual(self.names(declared), ["N.foo", "N.foo_assoc"])  # the nearest target is declared above
        farther = "def foo := 1\nnamespace N\nattribute [reassoc] foo\nend N\n"
        self.assertEqual(self.names(farther), ["foo", "?maybe:N.foo_assoc", "?maybe:foo_assoc"])  # N.foo may exist
        listed = "attribute [reassoc,\n  simp] _root_.MyNs.probe\n"
        self.assertEqual(self.names(listed), ["MyNs.probe_assoc"])  # an attribute list over two lines
        self.assertIn("?maybe:MyNs.probe_assoc", self.names("open MyNs in attribute [reassoc] probe\n"))
        renamed = "namespace X\nopen N renaming original → localName\nattribute [reassoc] localName\nend X\n"
        self.assertIn("?maybe:N.original_assoc", self.names(renamed))  # the name it stands for
        ascii_arrow = "namespace X\nopen N renaming original -> aliasName\nattribute [reassoc] aliasName.sub\nend X\n"
        self.assertIn("?maybe:N.original.sub_assoc", self.names(ascii_arrow))  # `->`, and a name under the alias
        next_line = "namespace X\nopen N renaming\n  original → localName\nattribute [reassoc] localName\nend X\n"
        self.assertIn("?maybe:N.original_assoc", self.names(next_line))  # the rename list on the next line
        self.assertEqual(self.names("attribute [reassoc] _root_.N.«right]bracket»\n"), ["N.«right]bracket_assoc»"])
        quoted = "namespace X\nopen N renaming «two words» → aliasName\nattribute [reassoc] aliasName\nend X\n"
        self.assertIn("?maybe:N.«two words_assoc»", self.names(quoted))
        alias = "namespace X\nopen N renaming original → «quoted alias»\nattribute [reassoc] «quoted alias»\nend X\n"
        self.assertIn("?maybe:N.original_assoc", self.names(alias))
        self.assertEqual(self.names("attribute\n  [reassoc] _root_.N.original\n"), ["N.original_assoc"])  # list on the next line
        self.assertEqual(self.names("open N renaming → broken\n"), ["?gen:open:root.N"])  # a rename it cannot read
        absolute = "namespace X\nopen _root_.N renaming original → localName\nattribute [reassoc] localName\nend X\n"
        self.assertIn("?maybe:N.original_assoc", self.names(absolute))
        self.assertNotIn("?maybe:X.N.original_assoc", self.names(absolute))  # `_root_.N` is N wherever it is opened
        self.assertIn("?maybe:«Two Words».original_assoc",
                      self.names("namespace X\nopen «Two Words»\nattribute [reassoc] original\nend X\n"))
        bracket = "attribute [reassoc] _root_.N.«bracket[»\ndef rootAfter := 1\n"
        self.assertEqual(self.names(bracket), ["N.«bracket[_assoc»", "rootAfter"])  # a bracket inside a quoted name
        self.assertEqual(self.names("attribute [reassoc,\n"), ["?gen:attribute:file"])  # open at the end
        wrapped = "namespace N\n#time def dup := 1\n#count_heartbeats in theorem h : True := trivial\nend N\n"
        self.assertEqual(self.names(wrapped), ["N.dup", "N.h"])  # the commands they wrap

    def test_a_second_command_on_one_line(self):
        self.assertEqual(self.names("namespace N\ndef a := 1 def b := 2\nend N\n"), ["N.a", "?gen:line:N.def"])
        plain = ("deriving instance Repr for Foo\nderiving noncomputable instance Repr for Foo\nclass inductive Bar | a\n"
                 "attribute [local instance 5] f\n")
        self.assertFalse([n for n in self.names(plain) if n.startswith("?")])  # one command each

    def test_private_fields_and_structures(self):
        text = ("namespace N\nstructure S where\n  x : Nat\n  private y : Nat\nprivate structure P where\n  mk' ::\n"
                "  a : Nat\nprivate structure Q extends S\nend N\n")
        self.assertEqual(self.names(text, local=True), ["N.S", "N.S.x", "?local:N.S.x", "?local:N.S.y", "N.S.mk",
                                                        "?local:N.P", "?local:N.P.mk'", "?local:N.P.a", "?local:N.Q",
                                                        "?local:N.Q.toS", "?local:N.Q.mk"])  # every field is a label too
        self.assertIn("?gen:structure:N.S", self.names("namespace N\nstructure S where x : Nat y : Bool\nend N\n"))  # two fields, one line
        self.assertIn("?gen:structure:N.S", self.names("namespace N\nstructure S where\n  (a : Nat) x : Nat\nend N\n"))  # mixed
        self.assertIn("N.S.«parent part»", self.names("namespace N\nstructure S extends «parent part» : P where\nend N\n"))
        self.assertIn("N.S.toParent", self.names("namespace N\nstructure S extends (Parent) where\nend N\n"))
        self.assertIn("?gen:structure:N.S", self.names("namespace N\nstructure S extends «Parent.Type» where\nend N\n"))
        named = self.names("namespace N\nstructure S extends parentPart : P, Q where\n  a : Nat\nend N\n", local=True)
        self.assertTrue({"N.S.parentPart", "?local:N.S.parentPart", "N.S.toQ"} <= set(named))  # its own name, else toQ
        self.assertNotIn("N.S.toparentPart", named)
        header = "namespace N\nprivate structure P extends S where\n  a : Nat\nend N\n"
        self.assertIn("?local:N.P.toS", self.names(header, local=True))  # `where` on the header line

    def test_scoped_to_a_namespace(self):
        text = ('namespace M\nscoped[N] notation "‖" x "‖" => x\nscoped[N] syntax (name := foo) "foo" : term\n'
                'theorem after : True := trivial\nscoped notation "z" => 1\nend M\n')
        self.assertEqual(self.names(text), ["?parser:N.«term‖_‖»", "N.foo", "M.after", "?parser:M.termZ"])
        split = ('namespace M\nscoped[N]\nnotation "quuxprobe" => 1\ntheorem after : True := trivial\n'
                 'scoped[N]\n@[simp]\ntheorem t2 : True := trivial\ntheorem back : True := trivial\nend M\n')
        self.assertEqual(self.names(split), ["?parser:N.termQuuxprobe", "M.after", "N.t2", "M.back"])  # for the next command
        self.assertEqual(self.names("namespace N\n@[reassoc] theorem «x.y» : True := trivial\nend N\n"),
                         ["N.«x.y»", "N.«x.y_assoc»"])  # the suffix goes inside the quoted component

    def test_namespace_name_on_the_next_line(self):
        self.assertEqual(self.names("namespace\n  Foo\ndef dup := 1\nend Foo\ndef top := 1\n"), ["Foo.dup", "top"])

    def test_namespaces_in_either_spelling(self):
        for text in ("namespace «N»\ndef a := 1\nend N\ndef dup := 1\n", "namespace N\ndef a := 1\nend «N»\ndef dup := 1\n"):
            self.assertEqual(self.names(text), ["N.a", "dup"])

    def test_raw_strings(self):
        text = 'namespace N\ndef payload := r#"x"\nnamespace Shadow\n"#\ndef dup := 1\ndef s := r"a\\"\ndef after := 2\nend N\n'
        self.assertEqual(self.names(text), ["N.payload", "N.dup", "N.s", "N.after"])

    def test_placed_declarations(self):
        texts = {"o1": "namespace X\ndef moved := 1\ndef stays := 2\nend X\n",
                 "n1": "namespace X\ndef stays := 2\nend X\n",
                 "n2": "namespace X\ndef moved := 1\ndef fresh := 3\nend X\n"}
        changes = [("o1", "n1", "MathlibExt/A.lean"), (preflight.ZERO_OID, "n2", "MathlibExt/B.lean")]
        placed = preflight.placed_declarations(changes, texts)
        self.assertEqual({k: v for k, v in placed.items() if not k.startswith("?eqns:")},
                         {"X.moved": [("MathlibExt/B.lean", 2)], "X.fresh": [("MathlibExt/B.lean", 3)]})
        self.assertIn("?eqns:X.fresh", placed)  # its reserved equation names

    def test_backtest_6645_6650(self):
        """The two pull requests that blocked the queue on 23 November 2026 share four names."""
        fixture = load("projspace_6645_6650.json")
        first = {name for name, _ in preflight.declarations(fixture["6645"]["text"]) if not name.startswith("?eqns:")}
        second = {name for name, _ in preflight.declarations(fixture["6650"]["text"]) if not name.startswith("?eqns:")}
        self.assertIn("AlgebraicGeometry.ProjSpace.grad0Equiv", first)
        self.assertEqual(sorted(first & second), fixture["shared"])


# --------------------------------------------------------------------------------------------------


class FakeResponse(io.BytesIO):
    def __init__(self, body: bytes, link: str = ""):
        super().__init__(body)
        self.headers = {"Link": link} if link else {}


class GitHubReadTests(unittest.TestCase):
    def setUp(self):
        self.fixture = load("github_6650.json")
        self.head = self.fixture["pulls/6650"]["head"]["sha"]
        self.runs = self.fixture["check_runs"]["check_runs"]

    def test_codex_approval_on_the_exact_head(self):
        summary = preflight.summarize_reviews(self.fixture["reviews"], self.head)
        self.assertEqual((summary["codex"]["state"], summary["codex"]["kind"]), ("APPROVED", "automatic"))
        self.assertEqual(summary["change_requests"], [])
        self.assertIsNone(preflight.summarize_reviews(self.fixture["reviews"], "0" * 40)["codex"])

    def test_latest_codex_verdict_and_human_change_requests(self):
        codex = self.fixture["reviews"][0]
        later = dict(codex, id=2, state="CHANGES_REQUESTED", submitted_at="2026-11-23T17:00:00Z")
        human = {"id": 3, "user": {"login": "someone"}, "state": "CHANGES_REQUESTED", "commit_id": "abc",
                 "submitted_at": "2026-11-23T15:00:00Z", "body": "please fix"}
        informal = dict(codex, id=4, submitted_at="2026-11-23T18:00:00Z",
                        body="<!-- codex-advisory-review -->\nThis is an informal review.")
        summary = preflight.summarize_reviews([human, codex, later, informal], self.head)
        self.assertEqual(summary["codex"]["state"], "CHANGES_REQUESTED")
        self.assertEqual([r["login"] for r in summary["change_requests"]], ["someone"])
        approved = dict(human, id=5, state="APPROVED", submitted_at="2026-11-23T16:00:00Z")
        self.assertEqual(preflight.summarize_reviews([human, approved], self.head)["change_requests"], [])
        comment = dict(codex, body="<!-- codex-comment-review -->\n## Codex review")
        self.assertEqual(preflight.summarize_reviews([comment], self.head)["codex"]["kind"], "comment")

    def test_codex_verdict_attests_the_review(self):
        responses, logs = github_6650()
        gh = FakeGitHub(responses, logs)
        review_id = self.fixture["reviews"][0]["id"]
        self.assertEqual(preflight.codex_attested(gh, self.runs, review_id), "pull_request")
        self.assertIsNone(preflight.codex_attested(gh, self.runs, review_id + 1))
        job = f"/repos/{REPO}/actions/jobs/{self.fixture['codex_verdict_job_id']}"
        gh.responses[job] = dict(gh.responses[job], run_id=1)  # the log's job belongs to another run
        self.assertIsNone(preflight.codex_attested(gh, self.runs, review_id))
        gh.responses[job] = dict(gh.responses[job], run_id=self.fixture["codex_verdict_run"]["id"])
        run = f"/repos/{REPO}/actions/runs/{self.fixture['codex_verdict_run']['id']}"
        gh.responses[run] = dict(gh.responses[run], path=".github/workflows/other.yml")
        self.assertIsNone(preflight.codex_attested(gh, self.runs, review_id))

    def test_codex_comment_review_attested_by_its_run(self):
        responses, logs = github_6650()
        review = dict(preflight.summarize_reviews(self.fixture["reviews"], self.head)["codex"], kind="comment")
        window = "2026-11-23T15%3A19%3A09Z..2026-11-23T16%3A10%3A09Z"
        listing = f"/repos/{REPO}/actions/workflows/codex.yml/runs?event={{}}&status=success&created={window}"
        responses[listing.format("issue_comment")] = {"workflow_runs": [
            {"id": 77, "path": ".github/workflows/codex.yml", "event": "issue_comment", "created_at": "2026-11-23T16:00:00Z"},
            {"id": 78, "path": ".github/workflows/other.yml", "event": "issue_comment", "created_at": "2026-11-23T16:01:00Z"}]}
        responses[listing.format("pull_request_review_comment")] = {"workflow_runs": []}
        responses[f"/repos/{REPO}/actions/runs/77/jobs?per_page=50"] = {"jobs": [
            {"id": 5, "name": "codex", "conclusion": "success"},
            {"id": self.fixture["codex_verdict_job_id"], "name": "codex-verdict", "conclusion": "success"}]}
        gh = FakeGitHub(responses, logs)
        self.assertEqual(preflight.codex_comment_attested(gh, review), ("issue_comment", False))
        self.assertNotIn(f"/repos/{REPO}/actions/runs/78/jobs?per_page=50", gh.calls)
        self.assertEqual(preflight.codex_comment_attested(gh, dict(review, id=1)), (None, False))
        self.assertEqual(preflight.codex_comment_attested(gh, dict(review, id=1), budget=0), (None, True))

    def test_review_comment_runs_belong_to_the_head(self):
        responses, logs = github_6650()
        review = dict(preflight.summarize_reviews(self.fixture["reviews"], self.head)["codex"], kind="comment")
        window = "2026-11-23T15%3A19%3A09Z..2026-11-23T16%3A10%3A09Z"
        listing = f"/repos/{REPO}/actions/workflows/codex.yml/runs?event={{}}&status=success&created={window}"
        responses[listing.format("issue_comment")] = {"workflow_runs": []}
        responses[listing.format("pull_request_review_comment")] = {"workflow_runs": [
            {"id": 80, "path": ".github/workflows/codex.yml", "event": "pull_request_review_comment",
             "head_sha": "9" * 40, "created_at": "2026-11-23T16:00:00Z"}]}  # another pull request's run
        responses[f"/repos/{REPO}/actions/runs/80/jobs?per_page=50"] = {"jobs": [
            {"id": self.fixture["codex_verdict_job_id"], "name": "codex-verdict", "conclusion": "success"}]}
        responses[f"/repos/{REPO}/actions/jobs/{self.fixture['codex_verdict_job_id']}"]["run_id"] = 80
        gh = FakeGitHub(responses, logs)
        self.assertEqual(preflight.codex_comment_attested(gh, review, head=self.head), (None, False))
        self.assertNotIn(f"/repos/{REPO}/actions/runs/80/jobs?per_page=50", gh.calls)
        responses[listing.format("pull_request_review_comment")]["workflow_runs"][0]["head_sha"] = self.head
        gh = FakeGitHub(responses, logs)
        self.assertEqual(preflight.codex_comment_attested(gh, review, head=self.head), (None, False))  # never counted:
        # another pull request with the same head, into another branch, runs its own codex.yml for such a comment
        both = ("issue_comment", "pull_request_review_comment")
        self.assertEqual(preflight.codex_comment_attested(gh, review, events=both, head=self.head),
                         ("pull_request_review_comment", False))  # what the head filter alone would accept

    def test_fork_automatic_review_attested_by_its_target_run(self):
        responses, logs = github_6650()
        review = preflight.summarize_reviews(self.fixture["reviews"], self.head)["codex"]
        window = "2026-11-23T15%3A19%3A09Z..2026-11-23T16%3A10%3A09Z"
        listing = f"/repos/{REPO}/actions/workflows/codex.yml/runs?event=pull_request_target&status=success&created={window}"
        responses[listing] = {"workflow_runs": [
            {"id": 79, "path": ".github/workflows/codex.yml", "event": "pull_request_target", "created_at": "2026-11-23T16:00:00Z"}]}
        responses[f"/repos/{REPO}/actions/runs/79/jobs?per_page=50"] = {"jobs": [
            {"id": self.fixture["codex_verdict_job_id"], "name": "codex-verdict", "conclusion": "success"}]}
        responses[f"/repos/{REPO}/actions/jobs/{self.fixture['codex_verdict_job_id']}"]["run_id"] = 79
        gh = FakeGitHub(responses, logs)
        self.assertEqual(preflight.codex_comment_attested(gh, review, events=("pull_request_target",)),
                         ("pull_request_target", False))

    def test_required_checks_from_the_rules(self):
        extra = {"type": "required_status_checks", "parameters": {"required_status_checks": [
            {"context": "build", "integration_id": 15368}, {"context": "build", "integration_id": 99}]}}
        gh = FakeGitHub({f"/repos/{REPO}/rules/branches/main": self.fixture["rules"] + [extra]})
        required = preflight.get_required(gh, "main")
        self.assertEqual([c["context"] for c in required], list(REQUIRED) + ["build"])
        self.assertEqual(required[-1]["integration_id"], 99)
        required = required[:-1]
        with self.assertRaises(preflight.Failure):  # rules that cannot be read stop the run
            preflight.get_required(FakeGitHub({}), "main")
        summary = preflight.summarize_checks(self.runs, required)
        self.assertEqual({c["conclusion"] for c in summary["required"]}, {"success"})
        self.assertEqual(summary["advisory_failed"], [])

    def test_job_names_of_a_workflow(self):
        text = ("name: CI\non:\n  pull_request:\njobs:\n  preflight:\n    runs-on: x\n    name: repository integrity\n"
                "    steps:\n      - name: not a job\n  build:  # no name: its id\n    runs-on: x\n"
                "  matrix:\n    name: \"test ${{ matrix.os }}\"\n  quoted:\n    name: 'check the graph'\n")
        self.assertEqual(preflight._job_names(text), ["repository integrity", "build", "check the graph"])
        odd = ('jobs:\n  guard:\n    "name": verify inputs\n  flow: {name: x}\n  merged:\n    <<: *defaults\n'
               '  block:\n    name: >-\n      folded\n  plain:\n    runs-on: x  # c\n  hashed:\n    name: "a # b"\n')
        self.assertEqual(preflight._job_names(odd), ["verify inputs", "plain", "a # b"])  # the rest stay unknown

    def test_required_checks_come_from_mains_workflow(self):
        actions = {"id": preflight.ACTIONS_APP_ID}
        genuine = {"id": 10, "name": "guard", "app": actions, "status": "completed", "conclusion": "failure",
                   "details_url": f"https://github.com/{REPO}/actions/runs/1/job/10"}
        added = dict(genuine, id=20, conclusion="success", details_url=f"https://github.com/{REPO}/actions/runs/2/job/20")
        associated = [{"number": 6650, "base": {"ref": "main"}}]
        gh = FakeGitHub({f"/repos/{REPO}/actions/runs/1": {"event": "pull_request", "pull_requests": associated,
                                                         "path": ".github/workflows/bump-guard.yml"},
                         f"/repos/{REPO}/actions/runs/2": {"event": "pull_request", "pull_requests": associated,
                                                         "path": ".github/workflows/added-by-the-pr.yml"}})
        required = [{"context": "guard", "integration_id": preflight.ACTIONS_APP_ID}]
        workflows = {"guard": {".github/workflows/bump-guard.yml"}}
        provenance = preflight.Provenance(gh, 6650, "main", workflows=workflows)
        summary = preflight.summarize_checks([genuine, added], required, [], provenance)["required"][0]
        self.assertEqual(summary["conclusion"], "failure")  # the newer same-name job of another workflow is skipped
        pathless = dict(genuine, id=30, conclusion="failure", details_url=f"https://github.com/{REPO}/actions/runs/3/job/30")
        older = dict(genuine, id=5, conclusion="success")
        gh.responses[f"/repos/{REPO}/actions/runs/3"] = {"event": "pull_request", "pull_requests": associated}
        fresh = preflight.Provenance(gh, 6650, "main", workflows=workflows)
        self.assertEqual(preflight.summarize_checks([older, pathless], required, [], fresh)["required"][0]["provenance"],
                         "unknown")  # a newer run that names no workflow is not skipped for an older success
        gh.responses[f"/repos/{REPO}/actions/runs/3"]["path"] = ".github/workflows/folded.yml"  # a job it could not read
        partly = preflight.Provenance(gh, 6650, "main", workflows=workflows, unreadable={".github/workflows/folded.yml"})
        self.assertEqual(preflight.summarize_checks([older, pathless], required, [], partly)["required"][0]["provenance"],
                         "unknown")  # not foreign: that file may define guard
        self.assertEqual(preflight._read_jobs("jobs:\n  a:\n    name: guard\n  b:\n    name: >-\n      guard\n"),
                         (["guard"], False))
        gh.responses[f"/repos/{REPO}/actions/runs/1"]["pull_requests"] = associated + [{"number": 7001, "base": {"ref": "main"}}]
        shared = preflight.Provenance(gh, 6650, "main", workflows=workflows)
        self.assertEqual(shared.whose(genuine), "unknown")  # another pull request with the same head may have run it
        gh.responses[f"/repos/{REPO}/actions/runs/1"]["pull_requests"] = associated
        undefined = preflight.Provenance(gh, 6650, "main", workflows={})
        self.assertEqual(preflight.summarize_checks([genuine, added], required, [], undefined)["required"][0]["provenance"],
                         "unknown")  # no workflow on main defines it

    def test_required_checks_from_this_pull_requests_runs(self):
        actions = {"id": preflight.ACTIONS_APP_ID}
        own = {"id": 10, "name": "repository integrity", "app": actions, "status": "completed", "conclusion": "failure",
               "details_url": f"https://github.com/{REPO}/actions/runs/1/job/10"}
        other = dict(own, id=20, conclusion="success", details_url=f"https://github.com/{REPO}/actions/runs/2/job/20")
        gh = FakeGitHub({f"/repos/{REPO}/actions/runs/1": {"event": "pull_request", "pull_requests": [
                             {"number": 6650, "base": {"ref": "main"}}]},
                         f"/repos/{REPO}/actions/runs/2": {"event": "pull_request", "pull_requests": [
                             {"number": 7001, "base": {"ref": "release"}}]}})
        required = [{"context": "repository integrity", "integration_id": preflight.ACTIONS_APP_ID}]
        provenance = preflight.Provenance(gh, 6650, "main")
        self.assertEqual(preflight.summarize_checks([own, other], required, [], provenance)["required"][0]
                         ["conclusion"], "failure")  # #7001's later success on the same commit does not count
        self.assertEqual(preflight.summarize_checks([own, other], required, [])["required"][0]["conclusion"], "success")
        # A newer run that cannot be tied to this pull request leaves the check unknown, not the older result.
        unread = dict(own, id=30, conclusion="failure", details_url=f"https://github.com/{REPO}/actions/runs/3/job/30")
        own_success = dict(own, conclusion="success")
        untied = preflight.summarize_checks([own_success, unread], required, [], provenance)["required"][0]
        self.assertEqual((untied["provenance"], untied["conclusion"]), ("unknown", "failure"))  # its failure still shows
        gh.responses[f"/repos/{REPO}/actions/runs/4"] = {"event": "pull_request", "pull_requests": []}
        unlisted = dict(own, id=40, conclusion="success", details_url=f"https://github.com/{REPO}/actions/runs/4/job/40")
        self.assertEqual(preflight.summarize_checks([own, unlisted], required, [], provenance)["required"][0]
                         ["provenance"], "unknown")
        # A fork's run names no pull request, and one fork branch can back pull requests to two bases.
        gh.responses[f"/repos/{REPO}/actions/runs/4"].update(head_repository={"full_name": "someone/fork"},
                                                             head_branch="topic")
        for number, base in ((6650, "main"), (7001, "release")):
            fork = preflight.Provenance(gh, number, base)
            self.assertEqual(preflight.summarize_checks([own, unlisted], required, [], fork)["required"][0]
                             ["provenance"], "unknown")
        unknown = {"name": "build", "status": "unknown", "conclusion": None, "url": None}
        guard = {"name": "guard", "status": "completed", "conclusion": "failure", "url": None}
        failed = preflight.evaluate(ready_facts(checks={"required": [unknown], "advisory_failed": []}), NOW)
        self.assertIn("cannot be tied to this pull request", failed["checks"][2]["detail"])
        self.assertIn("re-run those checks", failed["checks"][2]["next"])
        failed = preflight.evaluate(ready_facts(fork=True, checks={"required": [unknown], "advisory_failed": []}), NOW)
        self.assertTrue(failed["next"].startswith("only hand checks remain"))  # nothing else is wrong
        self.assertIn("its required checks and CI run, on its page", failed["next"])
        pending = {"name": "guard", "status": "in_progress", "conclusion": None, "url": None}
        mixed = ready_facts(fork=True, checks={"required": [unknown, pending], "advisory_failed": []},
                            duplicates={"names": 2, "found": [], "incomplete": None, "unpredictable": ["@[simps] on F.e"]})
        result = preflight.evaluate(mixed, NOW)
        self.assertIn("not finished on 1111111111: guard", result["checks"][2]["detail"])
        self.assertTrue(result["next"].startswith("wait for the required checks"))  # not the merge box yet
        both = preflight.evaluate(ready_facts(checks={"required": [unknown, guard], "advisory_failed": []}), NOW)
        self.assertIn("failed on 1111111111: guard (failure)", both["checks"][2]["detail"])
        self.assertIn("build on 1111111111 cannot be tied", both["checks"][2]["detail"])
        self.assertIn("read the failing step", both["checks"][2]["next"])  # the known failure comes first

    def test_ci_run_reads_runs_newest_first(self):
        actions = {"id": preflight.ACTIONS_APP_ID}
        builds = [{"id": i, "name": "build", "app": actions, "details_url": f"https://github.com/{REPO}/actions/runs/{i}/job/{i}"}
                  for i in range(1, 202)]
        responses = {f"/repos/{REPO}/actions/runs/{i}": {"event": "pull_request", "path": ".github/workflows/ci.yml",
                                                         "head_sha": "1" * 40, "pull_requests": [
                                                             {"number": 7000, "base": {"ref": "main"}}]}
                     for i in range(1, 202)}
        responses[f"/repos/{REPO}/actions/jobs/201"] = {"run_id": 201, "name": "build"}
        gh = FakeGitHub(responses)
        preflight.ci_run(gh, builds, "1" * 40, 7000, "main", preflight.Provenance(gh, 7000, "main"))
        self.assertEqual(len([c for c in gh.calls if "/actions/runs/" in c]), 1)  # the newest, and no other
        capped = preflight.Provenance(FakeGitHub({}), 7000, "main", budget=2)
        self.assertEqual(capped.latest(builds), (builds[-1], "unknown"))

    def test_latest_run_from_the_required_app(self):
        runs = copy.deepcopy(self.runs)
        build = next(r for r in runs if r["name"] == "build")
        runs.append(dict(build, id=build["id"] + 1, started_at=None, status="queued", conclusion=None))
        runs.append(dict(build, id=build["id"] + 2, name="graph sync", conclusion="failure"))
        guard = next(r for r in runs if r["name"] == "guard")
        runs.remove(guard)
        required = [{"context": "build", "integration_id": 15368}, {"context": "guard", "integration_id": 15368},
                    {"context": "legacy", "integration_id": None}]
        statuses = [{"context": "guard", "state": "success"}, {"context": "legacy", "state": "success"}]
        summary = {c["name"]: c for c in preflight.summarize_checks(runs, required, statuses)["required"]}
        self.assertEqual(summary["build"]["status"], "queued")  # the newer attempt, not the older success
        self.assertIsNone(summary["guard"]["status"])  # a status cannot stand in for a GitHub Actions check
        self.assertEqual(summary["legacy"]["conclusion"], "success")
        self.assertIn("graph sync", preflight.summarize_checks(runs, required, statuses)["advisory_failed"])

    def test_ci_base_from_the_checkout_log(self):
        responses, logs = github_6650()
        gh = FakeGitHub(responses, logs)
        ci = preflight.ci_run(gh, self.runs, self.head)
        self.assertEqual(ci["base"], "5c77d5224cebd12e0808329f65611358b2a85d9a")
        self.assertEqual(ci["created_at"], "2026-11-23T16:06:05Z")
        other = preflight.ci_run(gh, self.runs, "1" * 40)
        self.assertIsNone(other["base"])
        self.assertIn("for pull_request on 1eb2325e6b", other["base_error"])
        run = f"/repos/{REPO}/actions/runs/{self.fixture['run_id']}"
        gh.responses[run] = dict(gh.responses[run], path=".github/workflows/other.yml")
        self.assertIn("not .github/workflows/ci.yml", preflight.ci_run(gh, self.runs, self.head)["base_error"])
        gh.responses[run] = dict(gh.responses[run], path=".github/workflows/ci.yml")
        lower = dict(gh.responses[run], pull_requests=[{"number": 6650, "base": {"ref": "lower-feature"}}])
        gh.responses[run] = lower  # CI ran while the pull request targeted a stack's lower branch
        self.assertIn("tested it against lower-feature, not main",
                      preflight.ci_run(gh, self.runs, self.head, 6650, "main")["base_error"])
        gh.responses[run] = dict(lower, pull_requests=[{"number": 6650, "base": {"ref": "main"}}])
        self.assertIsNone(preflight.ci_run(gh, self.runs, self.head, 6650, "main")["base_error"])
        gh.responses[run] = dict(lower, pull_requests=[{"number": 7001, "base": {"ref": "release"}}])
        self.assertIn("its run is for #7001, not this pull request",
                      preflight.ci_run(gh, self.runs, self.head, 6650, "main")["base_error"])
        gh.responses[run] = dict(lower, pull_requests=[{"number": 6650, "base": {"ref": "main"}},
                                                       {"number": 7001, "base": {"ref": "main"}}])
        self.assertIn("its run also lists #7001, so which pull request it ran for is unknown",
                      preflight.ci_run(gh, self.runs, self.head, 6650, "main")["base_error"])
        gh.logs = {}
        self.assertIn("could not be read", preflight.ci_run(gh, self.runs, self.head)["base_error"])

    def test_only_a_pull_request_run_of_ci_can_skip_build(self):
        actions = {"id": preflight.ACTIONS_APP_ID}
        associated = [{"number": 6650, "base": {"ref": "main"}}]
        gh = FakeGitHub({f"/repos/{REPO}/actions/runs/{run}": {"event": event, "path": path, "pull_requests": associated}
                         for run, event, path in ((1, "pull_request", ".github/workflows/ci.yml"),
                                                  (2, "pull_request", ".github/workflows/source-diagnostics.yml"),
                                                  (3, "pull_request_target", ".github/workflows/ci.yml"))})

        def scoped(name: str, run: int, provenance=preflight.Provenance(gh, 6650, "main"), **changes) -> bool:
            check = dict({"id": run * 10, "name": name, "app": actions, "status": "completed", "conclusion": "skipped",
                          "details_url": f"https://github.com/{REPO}/actions/runs/{run}/job/{run * 10}"}, **changes)
            required = [{"context": name, "integration_id": preflight.ACTIONS_APP_ID}]
            return bool(preflight.summarize_checks([check], required, [], provenance)["required"][0].get("scoped"))
        self.assertTrue(scoped("build", 1))
        self.assertFalse(scoped("build", 1, conclusion="success"))  # not a skip
        self.assertFalse(scoped("repository integrity", 1))  # CI skips only build
        self.assertFalse(scoped("build", 2))  # a job named build in another workflow
        self.assertFalse(scoped("build", 3))  # not a pull_request run
        self.assertFalse(scoped("build", 1, provenance=None))  # a run it does not read
        self.assertFalse(scoped("build", 1, app={"id": 99}))  # another app

    def test_ci_base_from_the_scope_job_when_build_is_skipped(self):
        actions = {"id": preflight.ACTIONS_APP_ID}
        head, base = "1" * 40, "2" * 40

        def check(name: str, run: int, job: int, conclusion: str) -> dict:
            return {"id": job, "name": name, "app": actions, "status": "completed", "conclusion": conclusion,
                    "details_url": f"https://github.com/{REPO}/actions/runs/{run}/job/{job}"}
        build, scope = check("build", 5, 51, "skipped"), check(preflight.SCOPE_JOB, 5, 52, "success")
        responses = {f"/repos/{REPO}/actions/runs/5": {"event": "pull_request", "path": ".github/workflows/ci.yml",
                                                      "head_sha": head, "created_at": "2026-11-23T17:00:00Z",
                                                      "pull_requests": [{"number": 7000, "base": {"ref": "main"}}]},
                     f"/repos/{REPO}/actions/jobs/51": {"run_id": 5, "name": "build"},
                     f"/repos/{REPO}/actions/jobs/52": {"run_id": 5, "name": preflight.SCOPE_JOB}}
        logs = {52: f"2026-11-23T17:00:05Z HEAD is now at abcdef0 Merge {head} into {base}\n"}
        ci = preflight.ci_run(FakeGitHub(responses, logs), [build, scope], head, 7000, "main")
        self.assertEqual((ci["base"], ci["base_error"]), (base, None))
        # Another run's job, or a check run that points at another run's job, says nothing about this run.
        other = check(preflight.SCOPE_JOB, 6, 62, "success")
        self.assertIn(f"run 5 has no {preflight.SCOPE_JOB} job",
                      preflight.ci_run(FakeGitHub(responses, logs), [build, other], head, 7000, "main")["base_error"])
        responses[f"/repos/{REPO}/actions/jobs/52"] = {"run_id": 6, "name": preflight.SCOPE_JOB}
        self.assertIn(f"run 5 has no {preflight.SCOPE_JOB} job",
                      preflight.ci_run(FakeGitHub(responses, logs), [build, scope], head, 7000, "main")["base_error"])

    def test_a_heavy_rebuild_is_a_warning(self):
        def warned(built):
            result = preflight.evaluate(dict(ready_facts(), build_time=built), NOW)
            return result["ready"], [w for w in result["warnings"] if "heavy rebuild" in w]
        ready, heavy = warned({"minutes": 79, "median": 8, "sample": 20})
        self.assertTrue(ready)  # a warning, not a block
        self.assertEqual(len(heavy), 1)
        self.assertIn("79 min, against a median of 8 min over the last 20 pull request runs", heavy[0])
        self.assertEqual(warned({"minutes": 10, "median": 8, "sample": 20})[1], [])
        self.assertEqual(len(warned({"minutes": 50, "median": None, "sample": 0})[1]), 1)  # over 45 min
        self.assertEqual(warned(None)[1], [])
        workflow_runs = f"/repos/{REPO}/actions/workflows/ci.yml/runs?event=pull_request&status=success&per_page=20"
        def run(start, end, **more):
            return dict(run_started_at=start, updated_at=end, **more)
        answers = {f"/repos/{REPO}/actions/runs/99": run("2026-11-23T16:00:00Z", "2026-11-23T17:20:00Z", path=".github/workflows/ci.yml"),
                   workflow_runs: {"workflow_runs": [run("2026-11-23T10:00:00Z", "2026-11-23T10:08:00Z"),
                                                     run("2026-11-23T11:00:00Z", "2026-11-23T11:06:00Z"),
                                                     run("2026-11-23T12:00:00Z", "2026-11-23T12:10:00Z")]}}
        build = {"name": "build", "conclusion": "success", "started_at": "2026-11-23T16:00:00Z",
                 "completed_at": "2026-11-23T17:19:00Z", "run": 99}  # as summarize_checks authenticated it
        class Counted(FakeGitHub):
            calls = 0
            def get(self, path):
                Counted.calls += 1
                return super().get(path)
        self.assertEqual(preflight.build_time(Counted(answers), build), {"minutes": 80.0, "median": 8.0, "sample": 3})
        self.assertLessEqual(Counted.calls, 2)  # two requests, whatever the sample
        self.assertIsNone(preflight.build_time(FakeGitHub(answers), dict(build, conclusion="failure")))  # no successful build
        self.assertIsNone(preflight.build_time(FakeGitHub(answers), None))
        self.assertEqual(preflight.build_time(FakeGitHub({}), build), {"minutes": 79.0, "median": None, "sample": 0})  # no history
        class Cut(FakeGitHub):  # an answer cut short, or garbled: the history is unknown, nothing fails
            def get(self, path):
                raise json.JSONDecodeError("cut", "{", 1)
        self.assertEqual(preflight.build_time(Cut({}), build), {"minutes": 79.0, "median": None, "sample": 0})
        self.assertIsNone(preflight.build_time(FakeGitHub({}), dict(build, started_at="garbled")))

    def test_a_check_run_is_its_jobs_own(self):
        gh = FakeGitHub({f"/repos/{REPO}/actions/runs/100": {"event": "pull_request", "path": ".github/workflows/ci.yml",
                                                            "check_suite_id": 7, "pull_requests": [{"number": 6650, "base": {"ref": "main"}}]}})
        provenance = preflight.Provenance(gh, 6650, "main")
        genuine = {"id": 554, "name": "build", "app": {"id": preflight.ACTIONS_APP_ID}, "check_suite": {"id": 7},
                   "details_url": f"https://github.com/{REPO}/actions/runs/100/job/554"}
        self.assertEqual(provenance.whose(genuine), "ours")
        self.assertEqual(provenance.whose(dict(genuine, id=1554)), "foreign")  # minted through the API, pointing at a job
        self.assertEqual(provenance.whose(dict(genuine, check_suite={"id": 8})), "foreign")  # another suite
        answers = {f"/repos/{REPO}/actions/runs/900": {"path": ".github/workflows/codex.yml", "event": "pull_request",
                                                      "pull_requests": [{"number": 9999, "base": {"ref": "evil-base"}}]},
                   f"/repos/{REPO}/actions/jobs/901": {"run_id": 900, "name": "codex-verdict"}}
        verdict = {"id": 901, "name": "codex-verdict", "conclusion": "success", "app": {"id": preflight.ACTIONS_APP_ID},
                   "details_url": f"https://github.com/{REPO}/actions/runs/900/job/901"}
        class Logged(FakeGitHub):
            def read_log(self, job_id, pattern, max_bytes=0):
                return pattern.search("2026-11-23T16:00:00.0Z Codex approved review 77.")
        self.assertIsNone(preflight.codex_attested(Logged(answers), [verdict], 77, 6650, "main"))  # another PR's run
        answers[f"/repos/{REPO}/actions/runs/900"]["pull_requests"] = [{"number": 6650, "base": {"ref": "main"}}]
        self.assertEqual(preflight.codex_attested(Logged(answers), [verdict], 77, 6650, "main"), "pull_request")
        self.assertIsNone(preflight.codex_attested(Logged(answers), [dict(verdict, id=1901)], 77, 6650, "main"))

    def test_queue_snapshot_must_be_consistent(self):
        class Pages:
            repo = REPO

            def __init__(self, pages):
                self.pages, self.calls = pages, 0

            def graphql(self, query, variables, attempts=3):
                page = self.pages[self.calls % len(self.pages)]
                self.calls += 1
                return copy.deepcopy(page)
        first = queue_answer([(i, "a" * 40) for i in range(1, 101)], more=True)
        first["data"]["repository"]["mergeQueue"]["entries"]["totalCount"] = 101
        last = queue_answer([(101, "b" * 40)])
        last["data"]["repository"]["mergeQueue"]["entries"]["nodes"][0]["position"] = 101
        last["data"]["repository"]["mergeQueue"]["entries"]["totalCount"] = 101
        self.assertEqual(len(preflight.get_queue(Pages([first, last]), "main", 7000)["entries"]), 101)
        moved = copy.deepcopy(last)
        moved["data"]["repository"]["mergeQueue"]["entries"]["totalCount"] = 102  # the queue grew between pages
        pages = Pages([first, moved])
        with self.assertRaises(preflight.Failure):
            preflight.get_queue(pages, "main", 7000)
        self.assertEqual(pages.calls, 10)  # five complete reads, none agreeing with the one before
        swapped = queue_answer([(i, "a" * 40) for i in range(1, 51)] + [(102, "c" * 40)] + [(i, "a" * 40) for i in range(51, 100)],
                               more=True)  # #50 left and #102 came: same count, other members
        swapped["data"]["repository"]["mergeQueue"]["entries"]["totalCount"] = 101
        pages = Pages([first, last, swapped, last])  # each read consistent in itself, no two alike
        with self.assertRaises(preflight.Failure):
            preflight.get_queue(pages, "main", 7000)
        steady = Pages([first, last])
        self.assertEqual(len(preflight.get_queue(steady, "main", 7000)["entries"]), 101)
        self.assertEqual(steady.calls, 4)  # two complete reads that agree

    def test_queue_order_and_limits(self):
        gh = FakeGitHub({}, queue=queue_answer([(6645, "a" * 40), (6649, "b" * 40)]))
        queue = preflight.get_queue(gh, "main", 6650)
        self.assertEqual([e["number"] for e in queue["entries"]], [6645, 6649])
        self.assertIsNone(queue["own"])
        with self.assertRaises(preflight.Failure):
            preflight.get_queue(FakeGitHub({}, queue=queue_answer([(1, "a" * 40)], more=True)), "main", 2)

    def test_pagination_limit(self):
        gh = preflight.GitHub("t")
        pages = iter([FakeResponse(b"[1]", '<https://api.github.com/next>; rel="next"'), FakeResponse(b"[2]")])
        with mock.patch.object(gh, "_open", side_effect=lambda *a: next(pages)):
            self.assertEqual(gh.paged("/x"), [1, 2])
        endless = lambda *a: FakeResponse(b"[1]", '<https://api.github.com/next>; rel="next"')  # noqa: E731
        with mock.patch.object(gh, "_open", side_effect=endless), self.assertRaises(preflight.Failure):
            gh.paged("/x", max_pages=3)

    def test_token_of_the_active_account(self):
        two = ("github.com:\n    git_protocol: https\n    users:\n        first:\n            oauth_token: t_first\n"
               "        active:\n            oauth_token: t_active\n    user: active\n")
        self.assertEqual(preflight.hosts_token(two), "t_active")
        self.assertEqual(preflight.hosts_token(two + "    oauth_token: t_top\n"), "t_top")
        self.assertIsNone(preflight.hosts_token(two.replace("    user: active\n", "")))
        one = "github.com:\n    users:\n        only:\n            oauth_token: t_only\n"
        self.assertEqual(preflight.hosts_token(one), "t_only")
        self.assertIsNone(preflight.hosts_token(one + "    user: someone_else\n"))  # never another account
        self.assertIsNone(preflight.hosts_token("enterprise.example:\n    oauth_token: t_other\n"))
        with tempfile.TemporaryDirectory() as config:
            Path(config, "hosts.yml").write_text(two)
            with mock.patch.dict(os.environ, {"GH_CONFIG_DIR": config, "PATH": ""}, clear=True):
                self.assertEqual(preflight.read_token(), "t_active")
            with mock.patch.dict(os.environ, {"GH_CONFIG_DIR": config, "PATH": "", "GITHUB_TOKEN": "env"},
                                 clear=True):
                self.assertEqual(preflight.read_token(), "env")


# --------------------------------------------------------------------------------------------------


def git(cwd: Path, *args: str, input: str | None = None) -> str:
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t", GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_SYSTEM="/dev/null")
    return subprocess.run(["git", *args], cwd=cwd, input=input, text=True, capture_output=True, check=True,
                          env=env).stdout.strip()


FILLER = "".join(f"def filler{i} := {i}\n" for i in range(8))


# Bounding downloads needs --no-lazy-fetch (git 2.45); with an older git those runs refuse, so their tests skip.
LAZY_GUARD = subprocess.run(["git", "--no-lazy-fetch", "version"], capture_output=True).returncode == 0
NEEDS_GIT_245 = unittest.skipUnless(LAZY_GUARD, "needs git 2.45 or later (--no-lazy-fetch)")


class Remote:
    """A repository standing in for GitHub: main, and pull request heads under refs/pull/N/head."""

    def __init__(self, root: Path):
        self.path = root / "remote"
        self.path.mkdir()
        git(self.path, "init", "-q", "-b", "main")
        for key, value in (("uploadpack.allowFilter", "true"), ("uploadpack.allowAnySHA1InWant", "true")):
            git(self.path, "config", key, value)
        self.write({"lean-toolchain": "leanprover/lean4:v4.35.0\n", "lakefile.toml": "name = \"atlas\"\n",
                    "lake-manifest.json": "{}\n", "MathlibExt/A.lean": "namespace Foo\ndef a := 1\nend Foo\n",
                    "MathlibExt/S.lean": f"namespace Foo\n{FILLER}end Foo\n",
                    "MathlibExtTest/T.lean": "def testName := 1\n", **WORKFLOWS})
        with mock.patch.dict(os.environ, {"GIT_COMMITTER_DATE": "2026-11-01T00:00:00Z"}):
            self.main = self.commit("base")  # before the fixture's runs, so its workflows are not newer than them

    def write(self, files: dict[str, str]) -> None:
        for path, text in files.items():
            target = self.path / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        git(self.path, "add", "-A")

    def commit(self, message: str) -> str:
        git(self.path, "commit", "-q", "-m", message)
        return git(self.path, "rev-parse", "HEAD")

    def pull(self, number: int, files: dict[str, str], base: str | None = None) -> str:
        git(self.path, "checkout", "-q", "--detach", base or self.main)
        self.write(files)
        sha = self.commit(f"pull {number}")
        git(self.path, "update-ref", f"refs/pull/{number}/head", sha)
        git(self.path, "checkout", "-q", "main")
        return sha


class GitTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.remote = Remote(root)
        r = self.remote
        self.dup = r.pull(1, {"MathlibExt/B.lean": "namespace Foo\ntheorem dup : True := trivial\nend Foo\n",
                              "MathlibExtTest/U.lean": "def testName := 2\n"})
        self.bump = r.pull(2, {"lean-toolchain": "leanprover/lean4:v4.36.0\n"})
        self.edit = r.pull(3, {"MathlibExt/A.lean": "namespace Foo\ndef a := 3\nend Foo\n"})
        self.head = r.pull(10, {"MathlibExt/A.lean": "namespace Foo\ndef a := 10\nend Foo\n",
                                "MathlibExt/C.lean": "namespace Foo\ndef dup : Nat := 0\nend Foo\n",
                                "MathlibExtTest/V.lean": "def testName := 3\n"})
        self.git = preflight.Git(root / "cache" / "repo.git", f"file://{r.path}")
        self.git.ensure()
        self.fetch(1, 2, 3, 10)
        self.entries = [{"number": 1, "position": 1, "head": self.dup},
                        {"number": 2, "position": 2, "head": self.bump},
                        {"number": 3, "position": 3, "head": self.edit}]

    def fetch(self, *numbers: int) -> None:
        self.git.fetch(["+refs/heads/main:refs/preflight/main"] +
                       [f"+refs/pull/{n}/head:refs/preflight/pr/{n}" for n in numbers])

    def tearDown(self):
        self.tmp.cleanup()

    def simulate(self, main: str, entries: list[dict], head: str) -> tuple[dict, dict]:
        changes = preflight.head_changes(self.git, main, [head] + [e["head"] for e in entries])
        return preflight.simulate(self.git, main, entries, head, changes), changes

    def duplicates(self, main: str, entries: list[dict], head: str, since: str | None = None) -> dict:
        simulation, changes = self.simulate(main, entries, head)
        since = since or main
        return preflight.find_duplicates(self.git, main, since, preflight.merges_to_read(simulation, main),
                                         entries, changes, preflight.tested_names(self.git, since, head))

    def test_pins_from_the_merged_trees(self):
        r = self.remote
        bump = r.pull(104, {"lean-toolchain": "leanprover/lean4:v4.30.0\n"})
        late = r.pull(105, {"lean-toolchain": "leanprover/lean4:v4.31.0\n", "notes.txt": "late\n"})
        self.fetch(104, 105)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": 104, "position": 1, "head": bump}, {"number": 105, "position": 2, "head": late}]
        hidden = {bump: [], late: [], self.head: []}  # own diffs that do not show the pins, as a criss-cross can
        result = preflight.simulate(self.git, main, entries, self.head, hidden)
        self.assertEqual([(c["number"], c["files"]) for c in result["pin_changes_ahead"]],
                         [(104, ["lean-toolchain"]), (105, ["lean-toolchain"])])  # merged, and left out

    def test_ci_base_on_mains_first_parent_history(self):
        r = self.remote
        lower = r.pull(106, {"lower.txt": "lower\n"})
        git(r.path, "merge", "-q", "--no-ff", "-m", "Merge pull request #106 from x", lower)
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        main = self.git.rev_parse("refs/preflight/main")
        self.assertFalse(preflight.on_first_parent(self.git, lower, main))  # only a second parent of main
        self.assertTrue(preflight.on_first_parent(self.git, self.git.rev_parse(f"{main}~1"), main))
        self.assertTrue(preflight.on_first_parent(self.git, main, main))

    def test_git_runs_no_driver_that_a_pull_request_selects(self):
        r = self.remote
        marker = Path(self.tmp.name, "driver-ran")
        config = Path(self.tmp.name, "user.gitconfig")
        config.write_text(f'[merge "evil"]\n\tdriver = touch {marker}\n')
        r.write({"notes.txt": "base\n"})
        base = r.commit("Merge pull request #109 from x")
        r.write({"notes.txt": "main\n"})
        main = r.commit("Merge pull request #110 from x")
        head = r.pull(111, {"notes.txt": "pr\n", ".gitattributes": "notes.txt merge=evil\n"}, base=base)
        self.fetch(111)
        Path(self.git.dir, "info").mkdir(exist_ok=True)
        Path(self.git.dir, "info", "attributes").write_text("notes.txt merge=evil\n")  # as if attributes chose it
        control = dict(os.environ, GIT_CONFIG_GLOBAL=str(config))
        subprocess.run(["git", "--git-dir", str(self.git.dir), "merge-tree", "--write-tree", main, head],
                       env=control, capture_output=True)
        if marker.exists():  # with that configuration, this git runs the driver; some older ones never do
            marker.unlink()
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(config), "GIT_ATTR_SOURCE": head, "GH_TOKEN": "t"}):
            isolated = preflight.Git(self.git.dir, self.git.url)
        self.assertNotIn("GH_TOKEN", isolated.env)
        self.assertFalse(isolated.merge_tree(main, head)["clean"])
        self.assertFalse(marker.exists())

    def test_a_workflow_that_only_the_merge_changes(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        r.write({"notes.txt": "n0\n"})
        b0 = r.commit("Merge pull request #160 from x")
        git(r.path, "checkout", "-q", "--detach", b0)
        r.write({guard: "on: pull_request\njobs:\n  guard:\n    runs-on: y\n"})
        with mock.patch.dict(os.environ, {"GIT_COMMITTER_DATE": "2026-01-01T00:00:10Z"}):
            a1 = r.commit("a1")
        git(r.path, "checkout", "-q", "--detach", b0)
        r.write({"notes.txt": "n1\n"})
        with mock.patch.dict(os.environ, {"GIT_COMMITTER_DATE": "2026-01-01T00:00:20Z"}):
            c1 = r.commit("c1")  # the newer of the two merge bases, which git merge-base names
        git(r.path, "checkout", "-q", "--detach", c1)
        git(r.path, "merge", "-q", "--no-ff", "-m", "x", a1)  # x: both, the new workflow
        x = git(r.path, "rev-parse", "HEAD")
        git(r.path, "checkout", "-q", "--detach", a1)
        git(r.path, "merge", "-q", "--no-ff", "--no-commit", c1)
        git(r.path, "checkout", b0, "--", guard)  # y: both, with the old workflow back
        git(r.path, "commit", "-q", "-m", "y")
        r.write({"notes.txt": "n2\n"})
        head = r.commit("pull 161")
        git(r.path, "update-ref", "refs/pull/161/head", head)
        git(r.path, "update-ref", "refs/heads/main", x)
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        facts = {"base": "main", "ci": None, "queue": {"entries": []}, "check_workflows": [guard]}
        preflight.compute(self.git, facts, 161, head, x)
        self.assertEqual(facts["files"], ["notes.txt"])  # the diff from the merge base git names
        self.assertEqual(facts["changed_workflows"], [guard])  # but merging it into main changes the workflow

    def test_a_workflow_that_main_changed_after_ci(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        original = WORKFLOWS[guard]
        r.write({guard: original.replace("runs-on: x", "runs-on: changed")})
        tested_base = r.commit("Merge pull request #166 from x")  # main took a change to the workflow
        head = r.pull(167, {"notes.txt": "n\n"}, base=tested_base)
        git(r.path, "checkout", "-q", "main")
        r.write({guard: original})
        main = r.commit("Merge pull request #168 from x")  # and reverted it after CI ran
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": []}, "check_workflows": [guard]}
        preflight.compute(self.git, facts, 167, head, main)
        self.assertEqual((facts["changed_workflows"], facts["stale_workflows"]), ([], [guard]))
        facts.update(ready_facts(ci=facts["ci"], stale_workflows=[guard]), stale_workflows=[guard])
        freshness = next(c for c in preflight.evaluate(facts, NOW)["checks"] if c["name"] == "freshness")
        self.assertIn(f"CI ran its required checks with {guard}", " ".join(freshness["items"]))

    def test_a_workflow_changed_by_the_queue_ahead(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        blocker = r.pull(176, {guard: WORKFLOWS[guard].replace("runs-on: x", "runs-on: other")})
        ahead = r.pull(174, {guard: WORKFLOWS[guard].replace("runs-on: x", "runs-on: new")})  # the queue may skip it
        head = r.pull(175, {"notes.txt": "n\n"})
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        main = self.git.rev_parse("refs/preflight/main")
        facts = {"base": "main", "ci": {"base": main, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 176, "position": 1, "head": blocker},
                                       {"number": 174, "position": 2, "head": ahead}]}, "check_workflows": [guard]}
        preflight.compute(self.git, facts, 175, head, main)
        self.assertEqual(facts["workflows_ahead"], [{"number": 176, "position": 1, "path": guard},
                                                    {"number": 174, "position": 2, "path": guard}])
        result = preflight.evaluate(dict(ready_facts(), workflows_ahead=facts["workflows_ahead"][1:]), NOW)
        freshness = next(c for c in result["checks"] if c["name"] == "freshness")
        self.assertIn(f"#174, queued at position 2, changes {guard}", " ".join(freshness["items"]))
        self.assertTrue(result["next"].startswith("wait for #174 to land"))

    def test_a_workflow_that_only_an_alternative_queue_changes(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        other = r.pull(183, {guard: WORKFLOWS[guard].replace("runs-on: x", "runs-on: both")})  # stands for #2 and #3 together
        head = r.pull(184, {"notes.txt": "n\n"})
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main", "+refs/pull/183/head:refs/preflight/pr/183"])
        main = self.git.rev_parse("refs/preflight/main")
        merged = self.git.merge_tree(main, head)
        simulation = {"main": merged, "tip": main, "entries": [], "pin_changes_ahead": [],
                      "candidate": {"clean": True, "tree": merged["tree"],
                                    "alternatives": {"without #1": {"base": other, "tree": merged["tree"], "entries": []}}}}
        facts = {"base": "main", "ci": None, "queue": {"entries": []}, "check_workflows": [guard]}
        with mock.patch.object(preflight, "simulate", return_value=simulation), \
                mock.patch.object(preflight, "find_duplicates", return_value={}):
            preflight.compute(self.git, facts, 184, head, main)
        self.assertEqual(facts["workflows_ahead"], [{"number": None, "position": None, "path": guard}])

    def test_a_check_that_ran_before_its_workflow_changed(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        before = r.main
        r.write({ci: WORKFLOWS[ci] + "# changed\n"})
        change = r.commit("Merge pull request #900 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        activity = [{"timestamp": "2026-11-23T18:00:00Z", "before": before, "after": change},
                    {"timestamp": "2026-11-23T10:00:00Z", "before": "0" * 40, "after": before}]
        gh = FakeGitHub({f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day": activity,
                         f"/repos/{REPO}/actions/runs/1": {"path": ci, "created_at": "2026-11-23T17:00:00Z"},
                         f"/repos/{REPO}/actions/runs/2": {"path": ci, "created_at": "2026-11-23T19:00:00Z"},
                         f"/repos/{REPO}/actions/runs/3": {"path": ci}})
        provenance = preflight.Provenance(gh, 6650, "main")
        check = {"name": "build", "status": "completed", "conclusion": "success", "run": 1}
        self.assertEqual(preflight.stale_checks(gh, self.git, change, [check], provenance, now=NOW),
                         [{"name": "build", "path": ci, "main": before}])  # it ran on main before the change
        self.assertEqual(preflight.stale_checks(gh, self.git, change, [dict(check, run=2)], provenance, now=NOW), [])
        unknown = preflight.stale_checks(gh, self.git, change, [dict(check, run=3)], provenance, now=NOW)
        self.assertIn("unknown", unknown[0])  # no start time: not assumed fresh
        silent = FakeGitHub({f"/repos/{REPO}/actions/runs/1": {"path": ci, "created_at": "2026-11-23T17:00:00Z"}})
        unread = preflight.stale_checks(silent, self.git, change, [check], preflight.Provenance(silent, 6650, "main"), now=NOW)
        self.assertIn("unknown", unread[0])  # main's history unread: not assumed fresh either
        tie = FakeGitHub({f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day":
                          [{"timestamp": "2026-11-23T17:00:00Z", "before": before, "after": change}],
                          f"/repos/{REPO}/actions/runs/1": {"path": ci, "created_at": "2026-11-23T17:00:00Z"}})
        tied = preflight.stale_checks(tie, self.git, change, [check], preflight.Provenance(tie, 6650, "main"), now=NOW)
        self.assertIn("in the second its run started", tied[0]["unknown"])  # the order within that second is open
        r.write({"docs.txt": "d\n"})
        docs = r.commit("Merge pull request #901 from x")  # after the change, in the same second
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        same = [{"timestamp": "2026-11-23T18:00:00Z", "before": change, "after": docs},
                {"timestamp": "2026-11-23T18:00:00Z", "before": before, "after": change}]
        for listed in (same, same[::-1]):  # whatever order the two arrive in, main took them before -> change -> docs
            chained = FakeGitHub({f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day": listed,
                                  f"/repos/{REPO}/actions/runs/1": {"path": ci, "created_at": "2026-11-23T17:59:59Z"}})
            self.assertEqual(preflight.stale_checks(chained, self.git, docs, [check], preflight.Provenance(chained, 6650, "main"),
                                                    now=NOW), [{"name": "build", "path": ci, "main": before}])
        quiet = FakeGitHub({f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day": [],
                            f"/repos/{REPO}/actions/runs/1": {"path": ci, "created_at": "2026-11-23T17:00:00Z"}})
        self.assertEqual(preflight.stale_checks(quiet, self.git, change, [check], preflight.Provenance(quiet, 6650, "main"),
                                                now=NOW), [])  # no update in the day: main is as it was
        result = preflight.evaluate(dict(ready_facts(), stale_checks=[{"name": "build", "path": ci, "main": before}]), NOW)
        freshness = next(c for c in result["checks"] if c["name"] == "freshness")
        self.assertIn(f"build ran on main {before[:10]}, and main has changed {ci} since", " ".join(freshness["items"]))

    def test_an_indented_workflow_is_not_understood(self):
        r = self.remote
        r.write({".github/workflows/indented.yml": "  on: pull_request\n  jobs:\n    guard:\n      runs-on: x\n"})
        main = r.commit("Merge pull request #169 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        workflows, unreadable = preflight.workflow_jobs(self.git, main)
        self.assertEqual(unreadable, {".github/workflows/indented.yml"})
        actions = {"id": preflight.ACTIONS_APP_ID}
        older = {"id": 5, "name": "guard", "app": actions, "status": "completed", "conclusion": "success",
                 "details_url": f"https://github.com/{REPO}/actions/runs/1/job/5"}
        newer = dict(older, id=6, conclusion="failure", details_url=f"https://github.com/{REPO}/actions/runs/2/job/6")
        mine = [{"number": 6650, "base": {"ref": "main"}}]
        gh = FakeGitHub({f"/repos/{REPO}/actions/runs/1": {"event": "pull_request", "pull_requests": mine,
                                                         "path": ".github/workflows/bump-guard.yml"},
                         f"/repos/{REPO}/actions/runs/2": {"event": "pull_request", "pull_requests": mine,
                                                         "path": ".github/workflows/indented.yml"}})
        provenance = preflight.Provenance(gh, 6650, "main", workflows=workflows, unreadable=unreadable)
        required = [{"context": "guard", "integration_id": preflight.ACTIONS_APP_ID}]
        self.assertEqual(preflight.summarize_checks([older, newer], required, [], provenance)["required"][0]["provenance"],
                         "unknown")  # its newer failure is not skipped for the older success

    def test_code_that_the_required_checks_run(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: scripts/check.sh preflight\n      - run: cat docs/a.md\n",
                 "scripts/check.sh": "true\n", "docs/a.md": "a\n"})
        base = r.commit("Merge pull request #209 from x")
        script = r.pull(210, {"scripts/check.sh": "exit 0\n"}, base=base)
        itself = r.pull(211, {preflight.SELF: "# changed\n"}, base=base)
        docs = r.pull(212, {"docs/a.md": "b\n"}, base=base)
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        self.assertEqual(preflight.workflow_roots(self.git, base, [ci]), ["scripts"])  # code it runs, not docs it reads
        for number, head, changed, own in ((210, script, ["scripts/check.sh"], False),
                                           (211, itself, [preflight.SELF], True), (212, docs, [], False)):
            facts = {"base": "main", "ci": None, "queue": {"entries": []}, "check_workflows": [ci], "check_roots": ["scripts"]}
            preflight.compute(self.git, facts, number, head, base)
            self.assertEqual((facts["changed_dependencies"], facts["changes_self"]), (changed, own), number)
        result = preflight.evaluate(dict(ready_facts(), changed_dependencies=["scripts/check.sh"], changes_self=True), NOW)
        failed = {c["name"]: c for c in result["checks"] if not c["ok"]}
        self.assertEqual(sorted(failed), ["preflight", "workflows"])  # both hand checks
        self.assertTrue(result["next"].startswith("only hand checks remain"))
        gh = enqueue_github()
        self.assertEqual((preflight.enqueue(gh, result)["ok"], gh.mutations), (False, []))

    def test_each_check_and_the_code_it_runs(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        ci = ".github/workflows/ci.yml"
        r.write({guard: WORKFLOWS[guard] + "    steps:\n      - run: python3 scripts/bump/pinned_bump.py\n",
                 ci: WORKFLOWS[ci] + "    steps:\n      - run: scripts/check.sh\n",
                 "scripts/bump/pinned_bump.py": "import helper\n", "scripts/bump/helper.py": "x = 1\n",
                 "scripts/check.sh": "run scripts/test_scripts.sh\n", "scripts/test_scripts.sh": "true\n"})
        before = r.commit("Merge pull request #219 from x")
        r.write({"scripts/bump/helper.py": "x = 2\n"})
        changed = r.commit("Merge pull request #220 from x")  # main changed what guard runs, through an import
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        self.assertEqual(preflight.workflow_code(self.git, changed, [guard]), ["scripts/bump/helper.py", "scripts/bump/pinned_bump.py"])
        self.assertEqual(preflight.workflow_code(self.git, changed, [ci]), ["scripts/check.sh", "scripts/test_scripts.sh"])
        activity = [{"timestamp": "2026-11-23T17:30:00Z", "before": before, "after": changed}]
        gh = FakeGitHub({f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day": activity,
                         f"/repos/{REPO}/actions/runs/1": {"path": guard, "created_at": "2026-11-23T17:00:00Z"},
                         f"/repos/{REPO}/actions/runs/2": {"path": ci, "created_at": "2026-11-23T17:45:00Z"}})
        provenance = preflight.Provenance(gh, 6650, "main")
        required = [{"name": "guard", "status": "completed", "conclusion": "success", "run": 1},
                    {"name": "build", "status": "completed", "conclusion": "success", "run": 2}]
        code = {guard: preflight.workflow_code(self.git, changed, [guard]), ci: preflight.workflow_code(self.git, changed, [ci])}
        stale = preflight.stale_checks(gh, self.git, changed, required, provenance, now=NOW, code_by_workflow=code)
        self.assertEqual(stale, [{"name": "guard", "path": "scripts/bump/helper.py", "main": before}])  # a fresh build aside

    def test_what_a_glob_or_a_discovery_selects(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: scripts/run.sh\n",
                 "scripts/run.sh": "for f in scripts/checks/*.sh; do sh $f; done\n"
                                   "python3 -m unittest discover -s \"$REPO_ROOT/scripts/tests\" -p 'test_*.py'\n",
                 "scripts/checks/a.sh": "true\n", "scripts/checks/b.sh": "true\n", "scripts/tests/test_x.py": "pass\n"})
        tested_base = r.commit("Merge pull request #224 from x")
        head = r.pull(225, {"docs/c.md": "c\n"}, base=tested_base)
        added = r.pull(226, {"scripts/checks/new.sh": "false\n"}, base=tested_base)  # a check that would also run
        edited = r.pull(227, {"scripts/tests/test_x.py": "raise SystemExit(1)\n"}, base=tested_base)
        git(r.path, "checkout", "-q", "main")
        git(r.path, "rm", "-q", "scripts/checks/b.sh")
        main = r.commit("Merge pull request #228 from x")  # main stops running b.sh after CI ran it
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, main, [ci])
        self.assertEqual(code, ["glob:scripts/checks/*.sh", "scripts/checks/a.sh", "scripts/run.sh", "scripts/tests/"])
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 226, "position": 1, "head": added}, {"number": 227, "position": 2, "head": edited}]},
                 "check_workflows": [ci], "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 225, head, main)
        self.assertEqual(facts["stale_workflows"], ["glob:scripts/checks/*.sh"])  # what the glob selects changed
        self.assertEqual([(a["number"], a["path"]) for a in facts["workflows_ahead"]],
                         [(226, "glob:scripts/checks/*.sh"), (227, "scripts/tests/")])
        self.assertIn("?incomplete", preflight._code_closure(self.git, main, {"scripts/run.sh"}, limit=1))

    def test_modes_and_the_paths_a_glob_selects(self):
        r = self.remote
        git(r.path, "config", "core.fileMode", "false")  # modes set in the index alone
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: scripts/check.sh\n",
                 "scripts/check.sh": "for f in scripts/checks/*.sh; do sh $f; done\n", "scripts/checks/a.sh": "true\n",
                 "scripts/checks/child/unselected.sh": "true\n"})
        git(r.path, "update-index", "--chmod=+x", "scripts/check.sh")
        base = r.commit("Merge pull request #232 from x")
        head = r.pull(233, {"docs/d.md": "d\n"}, base=base)
        git(r.path, "checkout", "-q", "--detach", base)
        git(r.path, "update-index", "--chmod=-x", "scripts/check.sh")  # no longer executable: CI could not run it
        mode = r.commit("pull 234")
        git(r.path, "update-ref", "refs/pull/234/head", mode)
        git(r.path, "checkout", "-q", "main")
        accent = r.pull(235, {"scripts/checks/révision.sh": "false\n"}, base=base)  # the glob selects it
        nested = r.pull(236, {"scripts/checks/child/unselected.sh": "false\n"}, base=base)  # the glob does not
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, base, [ci])
        self.assertEqual(code, ["glob:scripts/checks/*.sh", "scripts/check.sh", "scripts/checks/a.sh"])
        facts = {"base": "main", "ci": {"base": base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 234, "position": 1, "head": mode}, {"number": 235, "position": 2, "head": accent},
                                       {"number": 236, "position": 3, "head": nested}]},
                 "check_workflows": [ci], "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 233, head, base)
        self.assertEqual([(a["number"], a["path"]) for a in facts["workflows_ahead"]],
                         [(234, "scripts/check.sh"), (235, "glob:scripts/checks/*.sh")])

    @NEEDS_GIT_245
    def test_sizes_before_downloading(self):
        r = self.remote
        first = r.pull(237, {"MathlibExt/Big1.lean": "def big1 := 1\n", "MathlibExt/Big2.lean": "def big2 := 2\n"})
        self.fetch(237)
        oids = {self.git.out("rev-parse", f"{first}:MathlibExt/Big1.lean"), self.git.out("rev-parse", f"{first}:MathlibExt/Big2.lean")}
        def present(oid):
            return subprocess.run(["git", "--git-dir", str(self.git.dir), "cat-file", "-e", oid], capture_output=True,
                                  env=dict(self.git.env, GIT_NO_LAZY_FETCH="1")).returncode == 0
        self.assertFalse(any(present(o) for o in oids))  # a blobless clone: not downloaded yet
        self.git.size_oracle = lambda wanted: {o: preflight.MAX_BLOB_BYTES + 1 for o in wanted}
        with self.assertRaisesRegex(preflight.Failure, "larger than"):
            self.git.blobs(oids)
        self.assertFalse(any(present(o) for o in oids))  # refused before downloading
        self.git.size_oracle = lambda wanted: {o: 6 for o in wanted}
        with mock.patch.object(preflight, "MAX_BLOBS_BYTES", 10), self.assertRaisesRegex(preflight.Failure, "would add up"):
            self.git.blobs(oids)
        self.assertFalse(any(present(o) for o in oids))
        one, two = sorted(oids)
        self.git.size_oracle = lambda wanted: {o: 6 for o in wanted}
        with mock.patch.object(preflight, "MAX_BLOBS_BYTES", 10):
            self.git.prefetch({one})  # 6 bytes reserved, then downloaded
            with self.assertRaisesRegex(preflight.Failure, "would add up"):
                self.git.prefetch({two})  # 12 over two requests: refused before the second
        self.assertEqual((present(one), present(two)), (True, False))
        self.git.size_oracle = lambda wanted: {}  # a size GitHub does not report: not downloaded
        self.git.prefetch({two})
        self.assertFalse(present(two))
        self.git.size_oracle = lambda wanted: {o: 6 for o in wanted}
        self.assertEqual(sorted(self.git.blobs(oids).values()), ["def big1 := 1\n", "def big2 := 2\n"])

    @NEEDS_GIT_245
    def test_a_merge_downloads_only_what_it_admits(self):
        r = self.remote
        left = r.pull(241, {"MathlibExt/A.lean": "namespace Foo\ndef a := 1\nend Foo\n-- left\n"})
        right = r.pull(242, {"MathlibExt/A.lean": "-- right\nnamespace Foo\ndef a := 1\nend Foo\n"})
        self.fetch(241, 242)
        self.git.size_oracle = lambda wanted: {o: preflight.MAX_MERGE_BLOB_BYTES + 1 for o in wanted}
        with self.assertRaises(preflight.Failure):  # its inputs are too large: no merge, and nothing downloaded
            self.git.merge_tree(left, right)
        sides = {self.git.out("rev-parse", f"{c}:MathlibExt/A.lean") for c in (left, right)}
        self.assertFalse(any(self.git.present(o) for o in sides))
        self.git.size_oracle = lambda wanted: {o: 50 for o in wanted}
        self.assertTrue(self.git.merge_tree(left, right)["clean"])  # admitted by size, then merged

    @NEEDS_GIT_245
    def test_a_merge_of_a_file_larger_than_preflight_reads(self):
        """Git merges a graph data file that both sides change, however much larger than the files that
        preflight parses it is (a 9 MB links file): only MAX_MERGE_BLOB_BYTES bounds its download. A
        .gitattributes stays within MAX_BLOB_BYTES, even when both sides change it."""
        r = self.remote
        lines = [f'{{"n": {i}}}' for i in range(40)]
        r.write({"blueprint/links/Combinatorics.jsonl": "\n".join(lines) + "\n"})
        base = r.commit("Merge pull request #384 from x")
        left = r.pull(385, {"blueprint/links/Combinatorics.jsonl": "\n".join(["{\"left\": 1}"] + lines) + "\n"}, base=base)
        right = r.pull(386, {"blueprint/links/Combinatorics.jsonl": "\n".join(lines + ["{\"right\": 1}"]) + "\n"}, base=base)
        self.fetch(385, 386)
        sizes = lambda oids: {o: int(git(r.path, "cat-file", "-s", o)) for o in oids}  # noqa: E731  as GitHub reports
        self.git.size_oracle = sizes
        with mock.patch.object(preflight, "MAX_BLOB_BYTES", 100):  # each side is over what preflight reads
            merged = self.git.merge_tree(left, right)
            self.assertTrue(merged["clean"], merged)  # but git merges it
            with self.assertRaisesRegex(preflight.Failure, "more than"):  # and preflight still does not read it
                self.git.blobs({self.git.out("rev-parse", f"{left}:blueprint/links/Combinatorics.jsonl")})
        fresh = preflight.Git(Path(self.tmp.name) / "fresh" / "repo.git", self.git.url)  # nothing downloaded yet
        fresh.ensure()
        fresh.fetch(["+refs/pull/385/head:refs/preflight/pr/385", "+refs/pull/386/head:refs/preflight/pr/386"])
        fresh.size_oracle = sizes
        with mock.patch.object(preflight, "MAX_MERGE_BLOB_BYTES", 100), \
                self.assertRaisesRegex(preflight.Failure, "merge-tree"):
            fresh.merge_tree(left, right)  # over the merge limit too: no merge, closed
        attributes = "*.jsonl merge=union\n" + "# " * 70 + "\n"
        ours = r.pull(387, {".gitattributes": attributes + "# ours\n"}, base=base)
        theirs = r.pull(388, {".gitattributes": "# theirs\n" + attributes}, base=base)
        cold = preflight.Git(Path(self.tmp.name) / "cold" / "repo.git", self.git.url)
        cold.ensure()
        cold.fetch(["+refs/pull/387/head:refs/preflight/pr/387", "+refs/pull/388/head:refs/preflight/pr/388"])
        cold.size_oracle = sizes
        with mock.patch.object(preflight, "MAX_BLOB_BYTES", 100), mock.patch.object(preflight, "MAX_MERGE_BLOB_BYTES", 1000), \
                self.assertRaisesRegex(preflight.Failure, "gitattributes"):
            cold.merge_tree(ours, theirs)  # an attribute file both sides change is a side too: still refused

    def test_files_the_checks_read(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: python3 scripts/inv.py scripts/requirements.txt\n",
                 "scripts/inv.py": "open('scripts/pins.json')\n", "scripts/requirements.txt": "a\n", "scripts/pins.json": "{}\n"})
        tested_base = r.commit("Merge pull request #252 from x")
        head = r.pull(253, {"docs/e.md": "e\n"}, base=tested_base)
        ahead = r.pull(254, {"scripts/pins.json": "{\"x\": 1}\n"}, base=tested_base)  # a queued PR changes what it reads
        git(r.path, "checkout", "-q", "main")
        r.write({"scripts/requirements.txt": "b\n"})
        main = r.commit("Merge pull request #255 from x")  # main changed a list the check reads, after CI
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, main, [ci])
        self.assertEqual(code, ["scripts/inv.py", "scripts/pins.json", "scripts/requirements.txt"])
        self.assertEqual(preflight.code_roots(code), ["scripts"])
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 254, "position": 1, "head": ahead}]}, "check_workflows": [ci],
                 "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 253, head, main)
        self.assertEqual(facts["stale_workflows"], ["scripts/requirements.txt"])
        self.assertEqual([(a["number"], a["path"]) for a in facts["workflows_ahead"]], [(254, "scripts/pins.json")])

    def test_inputs_main_lacks_and_data_globs(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: python3 scripts/pol.py\n",
                 "scripts/pol.py": "open('data/optional.txt')\nopen('data/gone.txt')\nglob('policies/*.json')\n",
                 "data/gone.txt": "g\n", "policies/a.json": "{}\n"})
        tested_base = r.commit("Merge pull request #256 from x")
        head = r.pull(257, {"docs/f.md": "f\n"}, base=tested_base)
        added = r.pull(258, {"data/optional.txt": "o\n"}, base=tested_base)  # a named input, absent until now
        edited = r.pull(259, {"policies/a.json": "{\"y\": 2}\n"}, base=tested_base)  # one the glob selects
        git(r.path, "checkout", "-q", "main")
        git(r.path, "rm", "-q", "data/gone.txt")
        main = r.commit("Merge pull request #260 from x")  # main removed an input the check read during CI
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, main, [ci])
        self.assertEqual(code, ["data/gone.txt", "data/optional.txt", "glob:policies/*.json", "policies/a.json", "scripts/pol.py"])
        self.assertEqual(preflight.code_roots(code), ["scripts"])  # inputs count for freshness, not for review
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 258, "position": 1, "head": added}, {"number": 259, "position": 2, "head": edited}]},
                 "check_workflows": [ci], "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 257, head, main)
        self.assertEqual(facts["stale_workflows"], ["data/gone.txt"])
        self.assertEqual([(a["number"], a["path"]) for a in facts["workflows_ahead"]],
                         [(258, "data/optional.txt"), (259, "glob:policies/*.json"), (259, "policies/a.json")])
        self.assertIn("?incomplete", preflight._code_closure(self.git, main, {"scripts/pol.py"}, limit=2))  # reads count

    def test_new_checkers_and_new_directories(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: python3 scripts/run2.py\n",
                 "scripts/run2.py": "if exists('tools/extra_validation.py'): run('tools/extra_validation.py')\nglob('policies2/*.json')\n"})
        base = r.commit("Merge pull request #261 from x")
        checker = r.pull(262, {"tools/extra_validation.py": "raise SystemExit(0)\n"}, base=base)  # a checker it runs, new
        policy = r.pull(263, {"policies2/one.json": "{}\n"}, base=base)  # the glob's first match, in a new directory
        head = r.pull(264, {"docs/g.md": "g\n"}, base=base)
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, base, [ci])
        self.assertEqual(code, ["glob:policies2/*.json", "scripts/run2.py", "tools/extra_validation.py"])
        facts = {"base": "main", "ci": None, "queue": {"entries": []}, "check_workflows": [ci], "check_code": code,
                 "check_roots": preflight.code_roots(code, lambda e: preflight.code_signature(self.git, base, e) is not None)}
        preflight.compute(self.git, facts, 262, checker, base)
        self.assertEqual(facts["changed_dependencies"], ["tools/extra_validation.py"])  # a maintainer reviews it
        facts = {"base": "main", "ci": None, "queue": {"entries": [{"number": 263, "position": 1, "head": policy}]},
                 "check_workflows": [ci], "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 264, head, base)
        self.assertEqual([(a["number"], a["path"]) for a in facts["workflows_ahead"]], [(263, "glob:policies2/*.json")])

    def test_signatures_keep_little(self):
        r = self.remote
        heads = [r.pull(265 + i, {f"docs/h{i}.md": f"{i}\n"}) for i in range(4)]
        self.fetch(*range(265, 269))
        self.git.watched = frozenset({"docs/h0.md", "glob:docs/*.md"})
        for h in heads:
            preflight.code_signature(self.git, h, "docs/h0.md")
        self.assertLessEqual(len(self.git.listings), 2)  # whole listings: the last two only
        self.assertEqual(set(self.git.signatures[heads[0]]), {"docs/h0.md", "glob:docs/*.md"})  # watched entries only

    @NEEDS_GIT_245
    def test_a_file_over_the_blob_limit_is_an_input_not_followed(self):
        r = self.remote
        big = "#" * 300
        r.write({"scripts/g.py": "open('scripts/map.json')\n", "scripts/map.json": '["scripts/named.py"]' + " " * 300,
                 "scripts/named.py": "pass\n", "scripts/h.py": "run('scripts/big.py')\nopen('scripts/same.txt')\n",
                 "scripts/big.py": big, "scripts/same.txt": big,  # one blob under two names
                 ".github/actions/a/action.yml": "runs:\n  using: composite\n" + "#" * 300})
        main = r.commit("Merge pull request #380 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        sizes = lambda oids: {o: int(git(r.path, "cat-file", "-s", o)) for o in oids}  # noqa: E731  as GitHub reports
        self.git.size_oracle = sizes
        self.assertIn("scripts/named.py", preflight._code_closure(self.git, main, {"scripts/g.py"}))
        cold = preflight.Git(Path(self.tmp.name) / "cold" / "repo.git", self.git.url)  # nothing downloaded yet
        cold.ensure()
        cold.fetch(["+refs/heads/main:refs/preflight/main"])
        cold.size_oracle = sizes
        with mock.patch.object(preflight, "MAX_BLOB_BYTES", 200):  # the map has grown past what preflight reads
            code = preflight._code_closure(cold, main, {"scripts/g.py"})
            self.assertIn("scripts/map.json", code)  # still an input: its changes count
            self.assertNotIn("scripts/named.py", code)  # but it is not opened
            self.assertNotIn("?incomplete", code)
            unread = git(r.path, "rev-parse", f"{main}:scripts/map.json")
            self.assertFalse(cold.present(unread))  # nor downloaded
            for start in ({"scripts/h.py"}, {".github/actions/a/action.yml"}):
                with self.assertRaises(preflight.Failure):  # a script, or an action that large, is not skipped
                    preflight._code_closure(self.git, main, start)

    def test_the_repositorys_own_checks_can_be_followed(self):
        """The code and inputs of this repository's required workflows, at its own HEAD, stay within the
        limit: an incomplete closure would make every pull request NOT READY."""
        root = Path(__file__).resolve().parents[2]
        found = subprocess.run(["git", "-C", str(root), "rev-parse", "--absolute-git-dir"], capture_output=True, text=True)
        workflows = [w for w in (".github/workflows/ci.yml", ".github/workflows/bump-guard.yml",
                                 ".github/workflows/source-diagnostics.yml") if (root / w).exists()]
        if found.returncode != 0 or not workflows:
            self.skipTest("not in a checkout of the repository")
        own = preflight.Git(Path(found.stdout.strip()), "https://github.com/facebookresearch/atlas-lean.git")
        head = own.out("rev-parse", "HEAD")
        for workflow in workflows:
            code = preflight.workflow_code(own, head, [workflow])
            self.assertNotIn("?incomplete", code, workflow)
            self.assertLess(len(code), 300, workflow)
            named = (root / workflow).read_text()  # a module the workflow names itself is its input; others are not
            self.assertFalse([c for c in code if c.endswith(".lean") and c.split("/", 1)[0] in preflight.LIBRARIES
                              and c not in named], workflow)
        # The paths that scripts/ci_scope.py and its test name are rules and examples, not inputs (NAMES_ONLY).
        self.assertEqual(preflight._code_closure(own, head, {"scripts/test_ci_scope.py"}),
                         {"scripts/test_ci_scope.py", "scripts/ci_scope.py"})

    def test_a_script_that_only_names_paths(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: python3 -I scripts/ci_scope.py x\n"
                                     "      - run: python3 scripts/other.py\n",
                 "scripts/ci_scope.py": "import sys\nimport helper\nDATA = {'scripts/data.json'}\n",
                 "scripts/helper.py": "x = 1\n", "scripts/other.py": "open('scripts/read.json')\n",
                 "scripts/data.json": "{}\n", "scripts/read.json": "{}\n"})
        base = r.commit("Merge pull request #300 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, base, [ci])
        self.assertTrue({"scripts/ci_scope.py", "scripts/helper.py", "scripts/other.py", "scripts/read.json"} <= set(code),
                        code)  # its imports are followed, and another script's names still count
        self.assertNotIn("scripts/data.json", code)

    def test_a_local_action(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - uses: ./.github/actions/setup\n",
                 ".github/actions/setup/action.yml": "runs:\n  using: composite\n  steps:\n    - run: python3 tools/verify.py\n      shell: bash\n",
                 "tools/verify.py": "x = 1\n"})
        base = r.commit("Merge pull request #286 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, base, [ci])
        self.assertTrue({".github/actions/setup/", ".github/actions/setup/action.yml", "tools/verify.py"} <= set(code), code)
        self.assertEqual(preflight.code_roots(code, lambda e: preflight.code_signature(self.git, base, e) is not None),
                         [".github", "tools"])

    def test_the_checkers_own_freshness(self):
        r = self.remote
        ci = ".github/workflows/ci.yml"
        r.write({ci: WORKFLOWS[ci] + "    steps:\n      - run: scripts/check.sh preflight\n      - run: cat .github/autoform-ref\n",
                 "scripts/check.sh": "true\n", ".github/autoform-ref": "v1\n"})
        tested_base = r.commit("Merge pull request #213 from x")
        head = r.pull(214, {"docs/b.md": "b\n"}, base=tested_base)
        ahead = r.pull(215, {".github/autoform-ref": "v3\n"}, base=tested_base)  # a queued PR moves the checker
        git(r.path, "checkout", "-q", "main")
        r.write({"scripts/check.sh": "exit 0\n"})
        main = r.commit("Merge pull request #216 from x")  # main changed the checker after CI ran
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, main, [ci])
        self.assertEqual(code, [".github/autoform-ref", "scripts/check.sh"])  # the revision it fetches counts as code
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 215, "position": 1, "head": ahead}]}, "check_workflows": [ci],
                 "check_code": code, "check_roots": [".github", "scripts"]}
        preflight.compute(self.git, facts, 214, head, main)
        self.assertEqual(facts["stale_workflows"], ["scripts/check.sh"])  # CI ran the older checker
        self.assertEqual(facts["workflows_ahead"], [{"number": 215, "position": 1, "path": ".github/autoform-ref"}])
        self.assertEqual(facts["changed_dependencies"], [])  # a docs change touches neither

    def test_compute_finds_a_queued_head_inside_the_candidate(self):
        r = self.remote
        lower = r.pull(112, {"MathlibExt/L.lean": "namespace Foo\ndef low := 1\nend Foo\n"})
        upper = r.pull(113, {"MathlibExt/U.lean": "namespace Foo\ndef up := 1\nend Foo\n"}, base=lower)
        facts = {"base": "main", "ci": None, "queue": {"entries": [{"number": 112, "position": 1, "head": lower}]}}
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        preflight.compute(self.git, facts, 113, upper, self.git.rev_parse("refs/preflight/main"))
        self.assertEqual(facts["contains_queued"], [112])  # an upper branch of a stack whose lower PR is queued

    def test_blob_sizes_are_bounded(self):
        r = self.remote
        head = r.pull(114, {"MathlibExt/Big.lean": "-- " + "x" * 2000 + "\n"})
        self.fetch(114)
        oid = self.git.out("rev-parse", f"{head}:MathlibExt/Big.lean")
        self.git.prefetch({oid})
        with mock.patch.object(preflight, "MAX_BLOB_BYTES", 1000), self.assertRaises(preflight.Failure):
            self.git.blobs({oid})
        with mock.patch.object(preflight, "MAX_BLOBS_BYTES", 1000), self.assertRaises(preflight.Failure):
            self.git.blobs({oid})
        self.assertIn(oid, self.git.blobs({oid}))
        small = r.pull(115, {"MathlibExt/Small.lean": "-- " + "y" * 900 + "\n"})
        self.fetch(115)
        other = self.git.out("rev-parse", f"{small}:MathlibExt/Small.lean")
        self.git.prefetch({other})
        fresh = preflight.Git(self.git.dir, self.git.url)
        with mock.patch.object(preflight, "MAX_BLOBS_BYTES", 2500):
            fresh.blobs({oid})
            fresh.blobs({oid})  # the same file again costs nothing more
            with self.assertRaises(preflight.Failure):  # one run's budget, across batches
                fresh.blobs({other})

    def test_merges_use_the_attributes_of_main(self):
        r = self.remote
        body = "".join(f"line {i}\n" for i in range(1, 12))
        r.write({".gitattributes": "f.txt -merge\n", "f.txt": body})
        base = r.commit("Merge pull request #116 from x")
        r.write({"f.txt": body.replace("line 1\n", "first\n")})
        main = r.commit("Merge pull request #117 from x")
        head = r.pull(118, {"f.txt": body.replace("line 11\n", "last\n")}, base=base)
        self.fetch(118)
        supported = self.git.run("--attr-source=" + preflight.EMPTY_TREE, "version", check=False).returncode == 0
        if supported:  # git 2.41 or later
            self.assertFalse(self.git.merge_tree(main, head)["clean"])  # as GitHub merges it: -merge makes a conflict
        self.git.attr_source = False  # a git without --attr-source refuses rather than merge the text
        with self.assertRaises(preflight.Failure):
            self.git.merge_tree(main, head)
        quoted = r.pull(119, {"Étale/.gitattributes": "f.txt -merge\n"}, base=r.main)  # only a path git quotes
        self.fetch(119)
        with self.assertRaises(preflight.Failure):
            self.git.merge_tree(quoted, head)

    def test_merges_ignore_the_users_attributes(self):
        r = self.remote
        r.write({"notes.txt": "base\n"})
        base = r.commit("Merge pull request #124 from x")
        r.write({"notes.txt": "main\n"})
        main = r.commit("Merge pull request #125 from x")
        head = r.pull(126, {"notes.txt": "pr\n"}, base=base)
        self.fetch(126)
        home = Path(self.tmp.name, "xdg")
        (home / "git").mkdir(parents=True)
        (home / "git" / "attributes").write_text("notes.txt merge=union\n")  # would make the conflict merge
        with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": str(home)}):
            influenced = preflight.Git(self.git.dir, self.git.url)
        self.assertEqual(influenced.merge_tree(main, head)["clean"], self.git.merge_tree(main, head)["clean"])
        self.assertFalse(influenced.merge_tree(main, head)["clean"])

    def test_parsers_whose_names_may_meet(self):
        r = self.remote
        plain = r.pull(137, {"MathlibExt/Pa1.lean": 'namespace N\nsyntax "quuxprobe" : term\nend N\n'})
        suffixed = r.pull(138, {"MathlibExt/Pa2.lean": 'namespace N\nsyntax "quuxprobe_1" : term\nend N\n'})
        dotted = r.pull(139, {"MathlibExt/Pa3.lean": 'namespace N\nsyntax "alpha.beta" : term\nend N\n'})
        theorem = r.pull(140, {"MathlibExt/Pa4.lean": "namespace N\ntheorem «termAlpha.beta» : True := trivial\nend N\n"})
        self.fetch(137, 138, 139, 140)
        main = self.git.rev_parse("refs/preflight/main")
        for (queued, number), head in (((plain, 137), suffixed), ((suffixed, 138), plain)):  # both orders
            result = self.duplicates(main, [{"number": number, "position": 1, "head": queued}], head)
            self.assertEqual(len(result["unpredictable"]), 1, result)  # termQuuxprobe_1 may be either one's
            self.assertEqual(result["found"], [])
        result = self.duplicates(main, [{"number": 139, "position": 1, "head": dotted}], theorem)
        self.assertIn("N.«termAlpha.beta»", result["unpredictable"][0])  # one component, dot and all

    def test_quoted_parser_and_category_names(self):
        r = self.remote
        parser = r.pull(145, {"MathlibExt/Q1.lean": 'namespace N\nsyntax (name := «two words») "probe" : term\nend N\n'})
        theorem = r.pull(146, {"MathlibExt/Q2.lean": "namespace N\ntheorem «two words» : True := trivial\nend N\n"})
        category = r.pull(147, {"MathlibExt/Q3.lean": "declare_syntax_cat «two words»\n"})
        twin = r.pull(148, {"MathlibExt/Q4.lean": "declare_syntax_cat «two words»\n"})
        self.fetch(145, 146, 147, 148)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h, name in (((parser, 145), theorem, "N.«two words»"), ((theorem, 146), parser, "N.«two words»"),
                                     ((category, 147), twin, "Lean.Parser.Category.«two words»")):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [(name, f"#{number}")])
        names = [n.split("#")[0] for n, _ in preflight.declarations('syntax (name := ) "x" : term\n')]
        self.assertEqual(names, ["?gen:syntax:syntax"])  # an explicit name it cannot read is not guessed at

    def test_unknown_parsers_against_predicted_ones(self):
        r = self.remote
        unknown = r.pull(149, {"MathlibExt/U1.lean": 'namespace N\nsyntax "probe" many(term) : term\nend N\n'})
        predicted = r.pull(150, {"MathlibExt/U2.lean": 'namespace N\nsyntax "probe" term : term\nend N\n'})
        dotted = r.pull(151, {"MathlibExt/U3.lean": "namespace N\ntheorem «a.b» : True := trivial\nend N\n"})
        self.fetch(149, 150, 151)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((unknown, 149), predicted), ((predicted, 150), unknown), ((unknown, 149), dotted)):
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"], (number, result))  # both may be termProbe_: a hand check

    def test_scoped_notations_may_meet(self):
        r = self.remote
        queued = r.pull(152, {"MathlibExt/Sc1.lean": 'scoped[N] notation "‖" x "‖" => x\n'})
        head = r.pull(153, {"MathlibExt/Sc2.lean": 'namespace N\nscoped notation "‖" y "‖" => y\nend N\n'})
        self.fetch(152, 153)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((queued, 152), head), ((head, 153), queued)):
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(any("N.«term‖_‖»" in item for item in result["unpredictable"]), result)

    def test_simps_on_a_quoted_name(self):
        r = self.remote
        queued = r.pull(154, {"MathlibExt/Sm1.lean": "namespace N\n@[simps apply] def «my.e» : Nat ≃ Nat := Equiv.refl _\nend N\n"})
        head = r.pull(155, {"MathlibExt/Sm2.lean": "namespace N\ntheorem «my.e_apply» : True := trivial\nend N\n"})
        self.fetch(154, 155)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((queued, 154), head), ((head, 155), queued)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"], (number, result))

    def test_nested_helpers_and_shared_lines(self):
        r = self.remote
        nested = r.pull(162, {"MathlibExt/Nh1.lean": "def f := g 1\nwhere\n  g (n : Nat) : Nat := h n\n  where\n    h (m : Nat) : Nat := m\n"})
        explicit = r.pull(163, {"MathlibExt/Nh2.lean": "def f.g.h : Nat := 2\n"})
        shared = r.pull(164, {"MathlibExt/Nh3.lean": "namespace N\ndef a := 1 def b := 2\nend N\n"})
        named = r.pull(165, {"MathlibExt/Nh4.lean": "namespace N\ndef b := 3\nend N\n"})
        self.fetch(162, 163, 164, 165)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((nested, 162), explicit), ((explicit, 163), nested)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("f.g.h", f"#{number}")])
        result = self.duplicates(main, [{"number": 164, "position": 1, "head": shared}], named)
        self.assertTrue(result["unpredictable"], result)  # its second command may declare N.b

    def test_shared_lines_parsers_and_quoted_let_rec(self):
        r = self.remote
        shared = r.pull(177, {"MathlibExt/Pl1.lean": "namespace N\ndef a := 1 def termQuuxprobe := 2\nend N\n"})
        parser = r.pull(178, {"MathlibExt/Pl2.lean": 'namespace N\nsyntax "quuxprobe" : term\nend N\n'})
        rec = r.pull(179, {"MathlibExt/Pl3.lean": "namespace N\ndef f : Nat :=\n  let rec «two words» : Nat := 1\n  1\nend N\n"})
        explicit = r.pull(180, {"MathlibExt/Pl4.lean": "def N.f.«two words» : Nat := 3\n"})
        self.fetch(177, 178, 179, 180)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((shared, 177), parser), ((parser, 178), shared)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["incomplete"], (number, result))
        for (q, number), h in (((rec, 179), explicit), ((explicit, 180), rec)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.f.«two words»", f"#{number}")])

    def test_duplicate_scan_parses_each_blob_once(self):
        r = self.remote
        same = "namespace Same\ndef many := 1\nend Same\n"
        queued = r.pull(185, {f"MathlibExt/Same{i}.lean": same for i in range(24)})
        head = r.pull(186, {"MathlibExt/Mine.lean": "def mine := 1\n"})
        self.fetch(185, 186)
        main = self.git.rev_parse("refs/preflight/main")
        real = preflight.declarations
        with mock.patch.object(preflight, "declarations", side_effect=real) as parse:
            self.duplicates(main, [{"number": 185, "position": 1, "head": queued}], head)
        self.assertLessEqual(sum(1 for call in parse.call_args_list if call.args[0] == same), 1)

    def test_an_unknown_command_may_declare_any_name(self):
        r = self.remote
        hashed = r.pull(200, {"MathlibExt/Mc3.lean": "namespace N\n#emit_def dup\nend N\n"})
        self.fetch(200)
        macro = r.pull(181, {"MathlibExt/Mc1.lean": "namespace N\nmy_macro dup\nend N\n"})
        plain = r.pull(182, {"MathlibExt/Mc2.lean": "def dup := 2\n"})
        self.fetch(181, 182)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((macro, 181), plain), ((plain, 182), macro), ((hashed, 200), plain), ((plain, 182), hashed)):
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["incomplete"], (number, result))

    def test_an_end_on_a_shared_line_and_quoted_helpers(self):
        r = self.remote
        ended = r.pull(170, {"MathlibExt/E5.lean": "namespace N\ndef a := 1 end N\ndef dup := 1\n"})
        root = r.pull(171, {"MathlibExt/E6.lean": "def dup := 2\n"})
        quoted = r.pull(172, {"MathlibExt/E7.lean": "namespace N\ndef f := 1\nwhere\n  «two words» : Nat := 2\nend N\n"})
        explicit = r.pull(173, {"MathlibExt/E8.lean": "def N.f.«two words» : Nat := 3\n"})
        self.fetch(170, 171, 172, 173)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((ended, 170), root), ((root, 171), ended)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["incomplete"] or result["found"], (number, result))
        for (q, number), h in (((quoted, 172), explicit), ((explicit, 173), quoted)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.f.«two words»", f"#{number}")])

    def test_module_local_names_clash_only_in_one_file(self):
        r = self.remote
        one = r.pull(187, {"WantedExt/W1.lean": "namespace N\ninstance_wanted instLocal : Inhabited Nat\nend N\n"})
        two = r.pull(188, {"WantedExt/W2.lean": "namespace N\ninstance_wanted instLocal : Inhabited Nat\nend N\n"})
        r.write({"WantedExt/W3.lean": "namespace N\n" + FILLER + "end N\n"})
        base = r.commit("Merge pull request #189 from x")
        top = r.pull(190, {"WantedExt/W3.lean": "namespace N\ntheorem_wanted shared : True\n" + FILLER + "end N\n"}, base=base)
        bottom = r.pull(191, {"WantedExt/W3.lean": "namespace N\n" + FILLER + "theorem_wanted shared : True\nend N\n"}, base=base)
        self.fetch(187, 188, 190, 191)
        main = self.git.rev_parse("refs/preflight/main")
        apart = self.duplicates(main, [{"number": 187, "position": 1, "head": one}], two)
        self.assertEqual(apart["found"], [])  # private placeholders in two modules do not clash
        together = self.duplicates(base, [{"number": 190, "position": 1, "head": top}], bottom)
        self.assertEqual([(d["name"], d["source"]) for d in together["found"]], [("N.shared", "#190")])  # one file

    def test_an_attribute_command_collides(self):
        r = self.remote
        queued = r.pull(193, {"MathlibExt/At1.lean": "namespace N\ntheorem foo : True := trivial\nattribute [reassoc] foo\nend N\n"})
        head = r.pull(194, {"MathlibExt/At2.lean": "namespace N\ntheorem foo_assoc : True := trivial\nend N\n"})
        self.fetch(193, 194)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((queued, 193), head), ((head, 194), queued)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.foo_assoc", f"#{number}")])

    def test_module_local_names_in_every_file_and_spelling(self):
        r = self.remote
        r.write({"WantedExt/Z.lean": "namespace N\n" + FILLER + "end N\n"})
        base = r.commit("Merge pull request #195 from x")
        top = r.pull(196, {"WantedExt/Z.lean": "namespace N\nprivate def «dup» := 1\n" + FILLER + "end N\n"}, base=base)
        bottom = r.pull(197, {"WantedExt/Z.lean": "namespace N\n" + FILLER + "private def dup := 2\nend N\n",
                              "WantedExt/A.lean": "namespace N\nprivate def dup := 3\nend N\n"}, base=base)
        self.fetch(196, 197)
        found = self.duplicates(base, [{"number": 196, "position": 1, "head": top}], bottom)["found"]
        self.assertEqual([(d["name"], d["source"], d["path"]) for d in found], [("N.dup", "#196", "WantedExt/Z.lean")])

    def test_possible_names_from_an_attribute_command(self):
        r = self.remote
        maybe = r.pull(198, {"MathlibExt/Pa5.lean": "namespace Outer\nopen Inner\nattribute [reassoc] foo\nend Outer\n"})
        explicit = r.pull(199, {"MathlibExt/Pa6.lean": "theorem Outer.Inner.foo_assoc : True := trivial\n"})
        self.fetch(198, 199)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((maybe, 198), explicit), ((explicit, 199), maybe)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertEqual(result["found"], [])
            self.assertTrue(result["unpredictable"], (number, result))
        self.assertEqual([n.split("#")[0] for n, _ in preflight.declarations("attribute [reassoc] 1x\n")],
                         ["?gen:attribute:1x"])  # a target it cannot read

    def test_possible_attribute_names_against_parsers(self):
        r = self.remote
        attr = r.pull(201, {"MathlibExt/Ap1.lean": "namespace N\nattribute [reassoc] termProbe\nend N\n"})
        parser = r.pull(202, {"MathlibExt/Ap2.lean": 'namespace N\nsyntax "probe_assoc" : term\nend N\n'})
        self.fetch(201, 202)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((attr, 201), parser), ((parser, 202), attr)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertEqual(result["found"], [])
            self.assertTrue(result["unpredictable"], (number, result))

    def test_reserved_equation_names(self):
        r = self.remote
        definition = r.pull(205, {"MathlibExt/Eq1.lean": "namespace N\ndef f : Nat → Nat\n  | 0 => 0\n  | n + 1 => n\nend N\n"})
        explicit = r.pull(206, {"MathlibExt/Eq2.lean": "theorem N.f.eq_1 : True := trivial\n"})
        self.fetch(205, 206)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((definition, 205), explicit), ((explicit, 206), definition)):  # both orders
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertEqual(result["found"], [])
            self.assertTrue(any("reserves" in item for item in result["unpredictable"]), (number, result))

    def test_reserved_equation_names_of_helpers(self):
        r = self.remote
        helper = r.pull(207, {"MathlibExt/Eq3.lean": "namespace N\ndef f : Nat := go 1\nwhere\n  go : Nat → Nat\n"
                                                     "    | 0 => 0\n    | n + 1 => go n\nend N\n"})
        explicit = r.pull(208, {"MathlibExt/Eq4.lean": "theorem N.f.go.eq_1 : True := trivial\n"})
        self.fetch(207, 208)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((helper, 207), explicit), ((explicit, 208), helper)):  # both orders
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(any("N.f.go.eq_1" in item for item in result["unpredictable"]), (number, result))

    def test_an_unknown_command_against_possible_names(self):
        r = self.remote
        macro = r.pull(203, {"MathlibExt/Um1.lean": "namespace N\nemit_assoc termProbe\nend N\n"})
        attr = r.pull(204, {"MathlibExt/Um2.lean": "namespace N\nattribute [reassoc] termProbe\nend N\n"})
        self.fetch(203, 204)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((macro, 203), attr), ((attr, 204), macro)):  # both orders: a hand check
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["incomplete"], (number, result))

    def test_a_field_label_whatever_its_visibility(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        r.write({"MathlibExt/Pv.lean": "namespace N\nstructure S where\n  a : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #229 from x")
        top = r.pull(230, {"MathlibExt/Pv.lean": "namespace N\nstructure S where\n  private x : Nat\n  a : Nat\n" + body + "end N\n"}, base=base)
        bottom = r.pull(231, {"MathlibExt/Pv.lean": "namespace N\nstructure S where\n  a : Nat\n" + body + "  x : Nat\nend N\n"}, base=base)
        self.fetch(230, 231)
        for (q, number), h in (((top, 230), bottom), ((bottom, 231), top)):  # private against public, both orders
            found = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.x", f"#{number}")])

    def test_a_parent_projection_is_a_label(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        start = "namespace N\nstructure P where\n  p : Nat\n"
        r.write({"MathlibExt/Pp.lean": start + "structure S where\n  a : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #238 from x")
        parent = r.pull(239, {"MathlibExt/Pp.lean": start + "structure S extends P where\n  a : Nat\n" + body + "end N\n"}, base=base)
        field = r.pull(240, {"MathlibExt/Pp.lean": start + "structure S where\n  a : Nat\n" + body + "  private toP : Nat\nend N\n"}, base=base)
        self.fetch(239, 240)
        for (q, number), h in (((parent, 239), field), ((field, 240), parent)):  # both orders
            found = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.toP", f"#{number}")])

    def test_an_unreadable_field_line_against_a_private_field(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        r.write({"MathlibExt/Pu.lean": "namespace N\nstructure S where\n  a0 : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #243 from x")
        groups = r.pull(244, {"MathlibExt/Pu.lean": "namespace N\nstructure S where\n  (a : Nat) (x : Nat)\n  a0 : Nat\n" + body + "end N\n"}, base=base)
        private = r.pull(245, {"MathlibExt/Pu.lean": "namespace N\nstructure S where\n  a0 : Nat\n" + body + "  private x : Nat\nend N\n"}, base=base)
        self.fetch(244, 245)
        for (q, number), h in (((groups, 244), private), ((private, 245), groups)):  # both orders: a hand check
            result = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["found"], (number, result))

    def test_a_named_parent_projection_is_a_label(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        start = "namespace N\nstructure P where\n  p : Nat\n"
        r.write({"MathlibExt/Pn.lean": start + "structure S where\n  a : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #246 from x")
        parent = r.pull(247, {"MathlibExt/Pn.lean": start + "structure S extends parentPart : P where\n  a : Nat\n" + body + "end N\n"}, base=base)
        field = r.pull(248, {"MathlibExt/Pn.lean": start + "structure S where\n  a : Nat\n" + body + "  private parentPart : Nat\nend N\n"}, base=base)
        self.fetch(247, 248)
        for (q, number), h in (((parent, 247), field), ((field, 248), parent)):  # both orders
            found = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.parentPart", f"#{number}")])

    def test_an_unreadable_field_line_in_two_files(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        r.write({"MathlibExt/Za.lean": "namespace N\nstructure S where\n  a0 : Nat\n" + body + "end N\n",
                 "MathlibExt/Aa.lean": "namespace N\nprivate structure S where\n  b0 : Nat\nend N\n"})  # the same N.S, first
        base = r.commit("Merge pull request #249 from x")
        groups = r.pull(250, {"MathlibExt/Za.lean": "namespace N\nstructure S where\n  (a : Nat) (x : Nat)\n  a0 : Nat\n" + body + "end N\n",
                              "MathlibExt/Aa.lean": "namespace N\nprivate structure S where\n  (a : Nat) (x : Nat)\n  b0 : Nat\nend N\n"}, base=base)
        private = r.pull(251, {"MathlibExt/Za.lean": "namespace N\nstructure S where\n  a0 : Nat\n" + body + "  private x : Nat\nend N\n"}, base=base)
        self.fetch(250, 251)
        for (q, number), h in (((groups, 250), private), ((private, 251), groups)):  # an unrelated file aside, both orders
            result = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(result["unpredictable"] or result["found"], (number, result))

    def test_a_command_elaborator_that_changes(self):
        r = self.remote
        r.write({"MathlibExt/Infra.lean": "namespace N\nelab_rules : command\n  | `(emit_dup) => addDecl `N.oldName\nend N\n",
                 "MathlibExt/Use.lean": "namespace N\nemit_dup\nend N\n"})
        base = r.commit("Merge pull request #274 from x")
        changed = r.pull(275, {"MathlibExt/Infra.lean": "namespace N\nelab_rules : command\n  | `(emit_dup) => addDecl `N.dup\nend N\n"}, base=base)
        same = r.pull(276, {"MathlibExt/Infra.lean": "namespace N\nelab_rules : command\n  | `(emit_dup) => addDecl `N.oldName\nend N\n-- note\n"}, base=base)
        candidate = r.pull(277, {"MathlibExt/New.lean": "namespace N\ndef dup := 1\nend N\n"}, base=base)
        self.fetch(275, 276, 277)
        result = self.duplicates(base, [{"number": 275, "position": 1, "head": changed}], candidate)
        self.assertTrue(any("elab_rules" in item for item in result["unpredictable"]), result)  # consumers unchanged, still a hand check
        result = self.duplicates(base, [{"number": 276, "position": 1, "head": same}], candidate)
        self.assertFalse(any("elab_rules" in item for item in result["unpredictable"]), result)  # the same elaborator

    def test_a_parent_that_may_be_an_alias(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        start = "namespace N\nstructure Parent where\n  p : Nat\nabbrev Alias := Parent\n"
        r.write({"MathlibExt/Al.lean": start + "structure S where\n  a : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #269 from x")
        alias = r.pull(270, {"MathlibExt/Al.lean": start + "structure S extends Alias where\n  a : Nat\n" + body + "end N\n"}, base=base)
        explicit = r.pull(271, {"MathlibExt/Al2.lean": "def N.S.toParent : Nat := 0\n"}, base=base)
        self.fetch(270, 271)
        for (q, number), h in (((alias, 270), explicit), ((explicit, 271), alias)):  # both orders: a hand check
            result = self.duplicates(base, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(any("toParent" in item for item in result["unpredictable"]), (number, result))

    def test_a_lowercase_parent_and_no_self_match(self):
        r = self.remote
        body = "".join(f"  f{i} : Nat\n" for i in range(8))
        start = "namespace N\nstructure lower where\n  p : Nat\nabbrev Alias := lower\n"
        r.write({"MathlibExt/Lw.lean": start + "structure S where\n  a : Nat\n" + body + "end N\n"})
        base = r.commit("Merge pull request #278 from x")
        alias = r.pull(279, {"MathlibExt/Lw.lean": start + "structure S extends Alias where\n  a : Nat\n" + body + "end N\n"}, base=base)
        explicit = r.pull(280, {"MathlibExt/Lw2.lean": "def N.S.tolower : Nat := 0\n"}, base=base)
        plain = r.pull(281, {"MathlibExt/Lw3.lean": "namespace M\nstructure P where\n  p : Nat\nstructure S extends P where\n  a : Nat\nend M\n"}, base=base)
        self.fetch(279, 280, 281)
        result = self.duplicates(base, [{"number": 279, "position": 1, "head": alias}], explicit)
        self.assertTrue(any("tolower" in item for item in result["unpredictable"]), result)  # Lean does not capitalise
        result = self.duplicates(base, [], plain)  # an empty queue: its own projection is no evidence
        self.assertEqual((result["found"], result["unpredictable"]), ([], set()) if isinstance(result["unpredictable"], set) else ([], []))

    def test_inputs_a_configuration_names(self):
        r = self.remote
        guard = ".github/workflows/bump-guard.yml"
        r.write({guard: WORKFLOWS[guard] + "    steps:\n      - run: python3 scripts/bump/guard2.py scripts/bump/deps2.json\n",
                 "scripts/bump/guard2.py": "import json\n", "scripts/bump/deps2.json": "{\"docs\": [\"README.md\", \"scripts/surface2.py\"]}\n",
                 "README.md": "readme\n", "scripts/surface2.py": "x = 1\n"})
        tested_base = r.commit("Merge pull request #282 from x")
        head = r.pull(283, {"docs/i.md": "i\n"}, base=tested_base)
        ahead = r.pull(284, {"scripts/surface2.py": "x = 2\n"}, base=tested_base)  # a queued PR changes a configured input
        git(r.path, "checkout", "-q", "main")
        r.write({"README.md": "changed\n"})
        main = r.commit("Merge pull request #285 from x")  # main changes another after the guard ran
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        code = preflight.workflow_code(self.git, main, [guard])
        self.assertTrue({"README.md", "scripts/surface2.py", "scripts/bump/deps2.json"} <= set(code), code)
        facts = {"base": "main", "ci": {"base": tested_base, "created_at": "2026-11-23T16:00:00Z", "base_error": None},
                 "queue": {"entries": [{"number": 284, "position": 1, "head": ahead}]}, "check_workflows": [guard],
                 "check_code": code, "check_roots": ["scripts"]}
        preflight.compute(self.git, facts, 283, head, main)
        self.assertIn("README.md", facts["stale_workflows"])
        self.assertIn((284, "scripts/surface2.py"), [(a["number"], a["path"]) for a in facts["workflows_ahead"]])

    def test_private_derived_instances_in_two_files(self):
        r = self.remote
        one = r.pull(272, {"MathlibExt/Pd1.lean": "namespace N\nprivate structure A where\n  x : Nat\n  deriving Inhabited\nend N\n"})
        two = r.pull(273, {"MathlibExt/Pd2.lean": "namespace N\nprivate structure A where\n  y : Nat\n  deriving Inhabited\nend N\n"})
        self.fetch(272, 273)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((one, 272), two), ((two, 273), one)):  # both orders: the instance may be public
            result = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)
            self.assertTrue(any("instInhabitedA" in item for item in result["unpredictable"]), (number, result))

    def test_a_long_file_reads_in_linear_time(self):
        text = "namespace N\n" + "emit_noop\n" * 20000 + "end N\n"
        start = time.monotonic()
        self.assertEqual(len(preflight.declarations(text)), 20000)
        self.assertLess(time.monotonic() - start, 10)

    def test_private_fields_clash_in_one_file(self):
        r = self.remote
        r.write({"MathlibExt/Pf.lean": "namespace N\nstructure S where\n  a : Nat\n" + "".join(f"  f{i} : Nat\n" for i in range(8)) + "end N\n"})
        base = r.commit("Merge pull request #221 from x")
        top = r.pull(222, {"MathlibExt/Pf.lean": "namespace N\nstructure S where\n  private x : Nat\n  a : Nat\n"
                           + "".join(f"  f{i} : Nat\n" for i in range(8)) + "end N\n"}, base=base)
        bottom = r.pull(223, {"MathlibExt/Pf.lean": "namespace N\nstructure S where\n  a : Nat\n"
                              + "".join(f"  f{i} : Nat\n" for i in range(8)) + "  private x : Nat\nend N\n"}, base=base)
        self.fetch(222, 223)
        found = self.duplicates(base, [{"number": 222, "position": 1, "head": top}], bottom)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.x", "#222")])

    def test_no_lean_changes_need_no_index_of_main(self):
        r = self.remote
        head = r.pull(192, {"notes.txt": "n\n"})
        self.fetch(192)
        main = self.git.rev_parse("refs/preflight/main")
        with mock.patch.object(preflight, "MAX_MAIN_CHANGES", 0):
            result = self.duplicates(main, [], head)
        self.assertEqual((result["names"], result["found"], result["incomplete"]), (0, [], None))

    def test_nested_modules_collide(self):
        r = self.remote
        queued = r.pull(217, {"MathlibExt/Deep/Er/Down/Q.lean": "namespace N\ndef nestedDup := 1\nend N\n"})
        head = r.pull(218, {"MathlibExt/Other/Place/H.lean": "namespace N\ndef nestedDup := 2\nend N\n"})
        self.fetch(217, 218)
        main = self.git.rev_parse("refs/preflight/main")
        changed = [path for _, _, path in self.git.diff_raw(main, head)]
        self.assertEqual(changed, ["MathlibExt/Other/Place/H.lean"])  # the library pathspec reaches nested modules
        found = self.duplicates(main, [{"number": 217, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.nestedDup", "#217")])

    def test_where_helpers_collide(self):
        r = self.remote
        queued = r.pull(157, {"MathlibExt/H1.lean": "def f : Nat := go where\n  go : Nat := 1\n"})
        head = r.pull(158, {"MathlibExt/H2.lean": "def f.go : Nat := 2\n"})
        self.fetch(157, 158)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((queued, 157), head), ((head, 158), queued)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("f.go", f"#{number}")])

    def test_a_scope_name_with_a_space(self):
        r = self.remote
        queued = r.pull(141, {"MathlibExt/Sp1.lean": "namespace «A B»\ndef helper := 1\nend «A B»\n"})
        head = r.pull(142, {"MathlibExt/Sp2.lean": "theorem «A B».helper : True := trivial\n"})
        self.fetch(141, 142)
        main = self.git.rev_parse("refs/preflight/main")
        for (q, number), h in (((queued, 141), head), ((head, 142), queued)):
            found = self.duplicates(main, [{"number": number, "position": 1, "head": q}], h)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("«A B».helper", f"#{number}")])

    def test_unnamed_syntax_against_a_named_parser(self):
        r = self.remote
        queued = r.pull(127, {"MathlibExt/Sy1.lean": 'namespace N\nsyntax "quuxprobe" : term\nend N\n'})
        parser = r.pull(128, {"MathlibExt/Sy2.lean": 'namespace N\nsyntax (name := termQuuxprobe) "other" : term\nend N\n'})
        theorem = r.pull(129, {"MathlibExt/Sy3.lean": "namespace N\ntheorem termQuuxprobe : True := trivial\nend N\n"})
        group = r.pull(130, {"MathlibExt/Sy4.lean": 'namespace N\nsyntax "bar" many(term) : term\nend N\n'})
        self.fetch(127, 128, 129, 130)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": 127, "position": 1, "head": queued}]
        hand = "the parser that a syntax command on #127 adds, named N.termQuuxprobe or N.termQuuxprobe_n, next to {}"
        for head in (parser, theorem):  # Lean names the queued parser N.termQuuxprobe, or that with a suffix
            result = self.duplicates(main, entries, head)
            self.assertEqual((result["found"], result["unpredictable"]), ([], [hand.format("N.termQuuxprobe")]))
        escaped = r.pull(133, {"MathlibExt/Sy5.lean": 'namespace N\nsyntax "\\u0071uuxprobe" : term\nend N\n'})
        suffixed = r.pull(134, {"MathlibExt/Sy6.lean": "namespace N\ntheorem termQuuxprobe_1 : True := trivial\n"
                                                       "theorem termQuuxprobe_10 : True := trivial\nend N\n"})
        self.fetch(133, 134)
        result = self.duplicates(main, [{"number": 133, "position": 1, "head": escaped}], theorem)
        self.assertEqual(result["unpredictable"], [hand.replace("#127", "#133").format("N.termQuuxprobe")])  # q
        result = self.duplicates(main, entries, suffixed)  # any suffix may be the one Lean takes
        self.assertEqual((result["found"], result["unpredictable"]), ([], [hand.format("N.termQuuxprobe_1")]))
        result = self.duplicates(main, [{"number": 130, "position": 1, "head": group}], theorem)
        self.assertEqual(result["unpredictable"],  # a name it cannot work out may be any name there
                         ["a syntax with no (name := ...) in N (#130), next to N.termQuuxprobe"])

    def test_nothing_to_prefetch(self):
        with mock.patch.object(self.git, "out") as out, mock.patch.object(self.git, "run") as run:
            self.git.prefetch(set())
            self.git.prefetch({preflight.ZERO_OID})
        self.assertEqual((out.call_count, run.call_count), (0, 0))

    def test_parser_names(self):
        cases = {("syntax", ' "quuxprobe" : term'): "termQuuxprobe", ("notation", ':50 a " ≈ " b => a = b'): "term_≈_",
                 ("infixl", ':65 " +++ " => f'): "term_+++_", ("prefix", ':max "√" => f'): "term√_",
                 ("postfix", ':max "!" => f'): "term_!", ("macro", ' "foo" x:term : term => x'): "termFoo_",
                 ("syntax", ' "a b" ident : tactic'): "tacticA_b_", ("syntax", ' "bar" many(term) : term'): None}
        for (keyword, after), name in cases.items():
            self.assertEqual(preflight._parser_name(keyword, after), name, (keyword, after))

    def test_workflow_jobs_on_main(self):
        r = self.remote
        r.write({".github/workflows/ci.yml": "on: pull_request\njobs:\n  build:\n    runs-on: x\n",
                 ".github/workflows/guard.yml": "on: pull_request\njobs:\n  g:\n    name: guard\n"})
        main = r.commit("Merge pull request #156 from x")
        self.git.ensure()
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        jobs, unreadable = preflight.workflow_jobs(self.git, main)
        self.assertEqual(unreadable, set())
        self.assertEqual((jobs["build"], jobs["guard"], jobs["source-diagnostics"]),
                         ({".github/workflows/ci.yml"}, {".github/workflows/bump-guard.yml", ".github/workflows/guard.yml"},
                          {".github/workflows/source-diagnostics.yml"}))
        self.assertNotIn("repository integrity", jobs)  # ci.yml no longer defines it

    def test_a_new_cache_takes_no_template(self):
        target = Path(self.tmp.name, "fresh.git")
        real = subprocess.run
        seen = []

        def clone_with_a_template(args, **kwargs):  # as an installation template would leave it
            seen.append(args)
            done = real(args, **kwargs)
            if "clone" in args:
                Path(target, "info").mkdir(exist_ok=True)
                Path(target, "info", "attributes").write_text("notes.txt merge=union\n")
            return done
        fresh = preflight.Git(target, self.git.url)
        with mock.patch.object(preflight.subprocess, "run", side_effect=clone_with_a_template):
            with self.assertRaises(preflight.Failure):
                fresh.ensure()  # refused right after cloning, before any merge
        self.assertIn("--template=", next(args for args in seen if "clone" in args))

    def test_a_cache_with_its_own_attributes_is_refused(self):
        self.git.ensure()  # a cache made by preflight, and reused
        Path(self.git.dir, "info").mkdir(exist_ok=True)
        Path(self.git.dir, "info", "attributes").write_text("notes.txt merge=union\n")
        with self.assertRaises(preflight.Failure):
            self.git.ensure()
        Path(self.git.dir, "info", "attributes").write_text("")
        self.git.ensure()

    def test_clone_is_blobless_full_and_checked(self):
        self.assertEqual(self.git.out("config", "remote.origin.partialclonefilter"), "blob:none")
        self.assertEqual(self.git.out("rev-parse", "--is-shallow-repository"), "false")
        self.git.ensure()  # a second run reuses it
        stranger = preflight.Git(Path(self.tmp.name) / "stranger.git", self.git.url)
        git(Path(self.tmp.name), "init", "-q", "--bare", "stranger.git")
        with self.assertRaises(preflight.Failure):
            stranger.ensure()
        with self.assertRaises(preflight.Failure):  # the clone of another repository
            preflight.Git(self.git.dir, "file:///elsewhere").ensure()

    def test_simulation_finds_pin_changes_and_the_conflicting_entry(self):
        main = self.git.rev_parse("refs/preflight/main")
        result, _ = self.simulate(main, self.entries, self.head)
        self.assertTrue(result["main"]["clean"])
        self.assertEqual([c["number"] for c in result["pin_changes_ahead"]], [2])
        self.assertEqual(result["pin_changes_ahead"][0]["files"], ["lean-toolchain"])
        self.assertFalse(result["candidate"]["clean"])
        self.assertEqual(result["candidate"]["conflicts_with"]["number"], 3)
        self.assertEqual(result["candidate"]["conflicts_with"]["files"], ["MathlibExt/A.lean"])
        alone, _ = self.simulate(main, self.entries[:2], self.head)
        self.assertTrue(alone["candidate"]["clean"])

    def test_entries_the_queue_may_keep(self):
        r = self.remote
        ahead = r.pull(6, {"notes.txt": "ahead\n"})
        behind = r.pull(7, {"notes.txt": "behind\n", "lean-toolchain": "leanprover/lean4:v4.37.0\n",
                            "MathlibExt/A.lean": "namespace Foo\ndef a := 7\nend Foo\n"})
        self.fetch(6, 7)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": 6, "position": 1, "head": ahead}, {"number": 7, "position": 2, "head": behind}]
        result, _ = self.simulate(main, entries, self.head)
        self.assertEqual([e["clean"] for e in result["entries"]], [True, False])
        self.assertEqual([c["number"] for c in result["pin_changes_ahead"]], [7])  # left out, but counted
        self.assertTrue(result["candidate"]["clean"])
        self.assertEqual([u["number"] for u in result["candidate"]["uncertain"]], [7])

    def test_left_out_entries_without_their_blocker(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        edit = lambda n: "".join(lines[:1] + [f"def filler0 := {n}\n"] + lines[2:])  # noqa: E731
        ahead = r.pull(26, {"MathlibExt/S.lean": edit(26), "lakefile.toml": 'name = "ahead"\n'})
        first = r.pull(27, {"MathlibExt/S.lean": edit(27)})
        second = r.pull(28, {"lakefile.toml": 'name = "second"\n'})
        head = r.pull(29, {"MathlibExt/N.lean": "namespace Foo\ndef fresh := 1\nend Foo\n"})
        self.fetch(26, 27, 28, 29)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(26, ahead), (27, first), (28, second)])]
        result, _ = self.simulate(main, entries, head)
        self.assertEqual([e["clean"] for e in result["entries"]], [True, False, False])
        self.assertEqual(list(result["candidate"]["alternatives"]), ["without #26"])
        self.assertEqual(result["candidate"]["alternatives"]["without #26"]["entries"], ["#27", "#28"])

    def test_every_union_of_blocker_sets(self):
        r = self.remote
        blockers, late = [], []
        for i in range(3):
            blockers.append(r.pull(97 + i, {f"f{i}.txt": "blocker\n"}))
            late.append(r.pull(100 + i, {f"f{i}.txt": "late\n"}))
        head = r.pull(103, {"MathlibExt/N.lean": "namespace Foo\ndef fresh := 1\nend Foo\n"})
        self.fetch(*range(97, 104))
        main = self.git.rev_parse("refs/preflight/main")
        order = [(97 + i, b) for i, b in enumerate(blockers)] + [(100 + i, e) for i, e in enumerate(late)]
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(order)]
        result, _ = self.simulate(main, entries, head)
        self.assertEqual(len(result["candidate"]["alternatives"]), 7)  # 2^3 - 1 unions of {#97}, {#98}, {#99}
        self.assertIn("without #97 and #99", result["candidate"]["alternatives"])

    def test_left_out_entry_with_the_entries_behind_it(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        blocker = r.pull(37, {"MathlibExt/S.lean": "".join(lines[:3] + ["def filler2 := 37\n"] + lines[4:]),
                              "lakefile.toml": 'name = "blocker"\n'})
        adds = r.pull(38, {"MathlibExt/S.lean": "".join(lines[:6] + ["def shared := 38\n"] + lines[6:]),
                           "lakefile.toml": 'name = "adds"\n'})
        bar = "".join(lines).replace("namespace Foo", "namespace Bar").replace("end Foo", "end Bar")
        renames = r.pull(39, {"MathlibExt/S.lean": bar})
        head = r.pull(40, {"MathlibExt/N.lean": "namespace Bar\ndef shared := 40\nend Bar\n"})
        self.fetch(37, 38, 39, 40)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(37, blocker), (38, adds), (39, renames)])]
        result, _ = self.simulate(main, entries, head)
        self.assertEqual([e["clean"] for e in result["entries"]], [True, False, True])
        self.assertEqual(result["candidate"]["alternatives"]["without #37"]["entries"], ["#38", "#39"])
        found = self.duplicates(main, entries, head)["found"]
        self.assertEqual([(d["name"], d["source"], d["other_path"]) for d in found],
                         [("Bar.shared", "#38 or #39", "MathlibExt/S.lean")])  # #38 adds it, #39 renames it

    def test_entry_with_two_blockers(self):
        r = self.remote
        first = r.pull(43, {"notes.txt": "first\n"})
        second = r.pull(44, {"lakefile.toml": 'name = "second"\n'})
        both = r.pull(45, {"notes.txt": "both\n", "lakefile.toml": 'name = "both"\n', "third.txt": "both\n"})
        head = r.pull(46, {"third.txt": "head\n"})
        self.fetch(43, 44, 45, 46)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(43, first), (44, second), (45, both)])]
        result, _ = self.simulate(main, entries, head)
        self.assertTrue(result["candidate"]["clean"])  # with the queue as it stands
        uncertain = result["candidate"]["uncertain"]
        self.assertEqual([(u["kept"], u["without"]) for u in uncertain], [([45], [43, 44])])

    def test_entry_that_an_earlier_entry_lets_merge(self):
        r = self.remote
        r.write({"X.txt": "base\n", "Z.txt": "base\n"})
        old = r.commit("Merge pull request #51 from x")
        late = r.pull(54, {"X.txt": "e\n", "lakefile.toml": 'name = "e"\n', "third.txt": "e\n"}, base=old)
        r.write({"X.txt": "main\n", "Z.txt": "main\n"})
        main = r.commit("Merge pull request #52 from x")  # now #54 conflicts with main
        fixer = r.pull(55, {"X.txt": "e\n"}, base=main)  # after it, #54 merges again
        blocker = r.pull(56, {"lakefile.toml": 'name = "b"\n'}, base=main)
        head = r.pull(57, {"third.txt": "head\n"}, base=main)
        self.fetch(54, 55, 56, 57)
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(55, fixer), (56, blocker), (54, late)])]
        result, _ = self.simulate(main, entries, head)
        self.assertTrue(result["candidate"]["clean"])  # with the queue as it stands
        self.assertEqual([(u["kept"], u["without"]) for u in result["candidate"]["uncertain"]], [([54], [56])])
        # With the blocker ahead of the fixer, no run of the queue admits #54, yet leaving #56 out does.
        swapped = [dict(entries[1], position=1), dict(entries[0], position=2), entries[2]]
        result, _ = self.simulate(main, swapped, head)
        self.assertEqual([(u["kept"], u["without"]) for u in result["candidate"]["uncertain"]], [([54], [56])])
        # A conflict with main in a file that no entry ahead changes: the queue removes it for sure.
        dead = r.pull(58, {"Z.txt": "dead\n"}, base=old)
        self.fetch(58)
        result, _ = self.simulate(main, entries[:2] + [{"number": 58, "position": 3, "head": dead}], head)
        self.assertEqual((result["candidate"]["uncertain"], result["candidate"]["alternatives"]), ([], {}))

    def test_attribute_changes_may_fix_a_conflict(self):
        r = self.remote
        r.write({"sub/x.txt": "base\n"})
        old = r.commit("Merge pull request #120 from x")
        late = r.pull(121, {"sub/x.txt": "late\n"}, base=old)
        r.write({"sub/x.txt": "main\n"})
        main = r.commit("Merge pull request #122 from x")  # now #121 conflicts with main in sub/x.txt
        attributes = r.pull(123, {".gitattributes": "sub/x.txt merge=union\n"}, base=main)  # touches no conflicted path
        self.fetch(121, 123)
        entries = [{"number": 123, "position": 1, "head": attributes}, {"number": 121, "position": 2, "head": late}]
        if self.git.run("--attr-source=" + preflight.EMPTY_TREE, "version", check=False).returncode == 0:
            self.assertNotEqual(preflight._admit(self.git, main, entries, entries[1]), "removed")
        else:  # git before 2.41 cannot merge with those attributes: preflight refuses rather than guess
            with self.assertRaises(preflight.Failure):
                preflight._admit(self.git, main, entries, entries[1])

    def test_fixer_across_a_rename_on_main(self):
        r = self.remote
        body = "".join(f"line {i}\n" for i in range(1, 12))
        r.write({"old.txt": "base\n" + body})
        old = r.commit("Merge pull request #66 from x")
        late = r.pull(67, {"old.txt": "e\n" + body, "lakefile.toml": 'name = "e"\n', "third.txt": "e\n"}, base=old)
        r.write({"old.txt": "main\n" + body})
        moved = r.commit("Merge pull request #68 from x")  # now #67 conflicts with main
        fixer = r.pull(69, {"old.txt": "e\n" + body}, base=moved)  # its own diff names old.txt
        git(r.path, "mv", "old.txt", "new.txt")
        main = r.commit("Merge pull request #70 from x")  # main renames the file the fixer changes
        blocker = r.pull(71, {"lakefile.toml": 'name = "b"\n'}, base=main)
        head = r.pull(72, {"third.txt": "head\n"}, base=main)
        self.fetch(67, 69, 71, 72)
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(69, fixer), (71, blocker), (67, late)])]
        result, _ = self.simulate(main, entries, head)
        self.assertEqual([(u["kept"], u["without"]) for u in result["candidate"]["uncertain"]], [([67], [71])])

    def test_fixer_through_shared_history(self):
        r = self.remote
        r.write({"x.txt": "base\n"})
        old = r.commit("Merge pull request #79 from x")
        first = r.pull(80, {"x.txt": "e\n"}, base=old)
        late = r.pull(80, {"lakefile.toml": 'name = "e"\n', "z.txt": "e\n"}, base=first)
        r.write({"x.txt": "main\n"})
        main = r.commit("Merge pull request #81 from x")  # now #80 conflicts with main in x.txt
        git(r.path, "checkout", "-q", "--detach", first)
        git(r.path, "merge", "-q", "--no-edit", "-X", "theirs", main)  # resolves x.txt as main has it
        r.write({"notes.txt": "fixer\n"})
        fixer = r.commit("only notes.txt differs from main")
        git(r.path, "update-ref", "refs/pull/82/head", fixer)
        git(r.path, "checkout", "-q", "main")
        blocker = r.pull(83, {"lakefile.toml": 'name = "b"\n'}, base=main)
        head = r.pull(84, {"z.txt": "head\n"}, base=main)
        self.fetch(80, 82, 83, 84)
        for order in ([(82, fixer), (83, blocker)], [(83, blocker), (82, fixer)]):
            entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(order + [(80, late)])]
            result, _ = self.simulate(main, entries, head)
            self.assertEqual([(u["kept"], u["without"]) for u in result["candidate"]["uncertain"]], [([80], [83])])

    def test_criss_cross_history_is_not_proof_of_removal(self):
        r = self.remote
        r.write({"x.txt": "base\n"})
        old = r.commit("Merge pull request #88 from x")
        r.write({"x.txt": "main\n"})
        m0 = r.commit("Merge pull request #89 from x")
        first = r.pull(90, {"x.txt": "e\n"}, base=old)
        git(r.path, "checkout", "-q", "--detach", m0)
        git(r.path, "merge", "-q", "--no-edit", "-X", "ours", first)
        r.write({"notes.txt": "a\n"})
        fixer = r.commit("a: main's x.txt, and notes")
        git(r.path, "checkout", "-q", "--detach", first)
        git(r.path, "merge", "-q", "--no-edit", "-X", "ours", m0)
        r.write({"lakefile.toml": 'name = "e"\n', "z.txt": "e\n"})
        late = r.commit("e: its x.txt, and more")
        for number, sha in ((91, fixer), (90, late)):
            git(r.path, "update-ref", f"refs/pull/{number}/head", sha)
        git(r.path, "checkout", "-q", "main")
        r.write({"x.txt": "main2\n"})
        main = r.commit("Merge pull request #92 from x")  # #90 conflicts with main in x.txt
        blocker = r.pull(93, {"lakefile.toml": 'name = "b"\n'}, base=main)
        self.fetch(90, 91, 93)
        bases = self.git.out("merge-base", "--all", fixer, late).split()
        self.assertEqual(sorted(bases), sorted([m0, first]))  # one base on main, one outside it
        entries = [{"number": n, "position": i + 1, "head": sha} for i, (n, sha) in enumerate(
            [(91, fixer), (93, blocker), (90, late)])]
        self.assertNotEqual(preflight._admit(self.git, main, entries, entries[2]), "removed")

    def test_ci_merge_that_cannot_be_reproduced(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        head = r.pull(47, {"MathlibExt/S.lean": "".join(lines[:4] + ["def filler3 := 47\n"] + lines[5:])})
        side = r.pull(48, {"MathlibExt/S.lean": "".join(lines[:4] + ["def filler3 := 48\n"] + lines[5:])})
        self.fetch(47, 48)
        self.assertIsNone(preflight.tested_names(self.git, side, head))
        main = self.git.rev_parse("refs/preflight/main")
        simulation, changes = self.simulate(main, [], head)
        result = preflight.find_duplicates(self.git, main, main, preflight.merges_to_read(simulation, main), [],
                                           changes, None)
        self.assertIn("that CI built does not merge cleanly here", result["incomplete"])

    def test_derived_instances_collide(self):
        r = self.remote
        queued = r.pull(49, {"MathlibExt/D1.lean": "namespace N\nderiving instance DecidableEq for Var\nend N\n"})
        head = r.pull(50, {"MathlibExt/D2.lean": "namespace N\nderiving instance DecidableEq for Var\nend N\n"})
        self.fetch(49, 50)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 49, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"], d["other_path"]) for d in found],
                         [("N.instDecidableEqVar", "#49", "MathlibExt/D1.lean")])

    def test_derived_instances_over_two_lines_collide(self):
        r = self.remote
        queued = r.pull(59, {"MathlibExt/D3.lean": "namespace N\nderiving instance DecidableEq for Var\nend N\n"})
        head = r.pull(60, {"MathlibExt/D4.lean": "namespace N\nderiving instance DecidableEq for\n  Var\nend N\n"})
        self.fetch(59, 60)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 59, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.instDecidableEqVar", "#59")])

    def test_generated_recursor_collides(self):
        r = self.remote
        queued = r.pull(61, {"MathlibExt/R1.lean": "namespace N\ninductive S where | a\nend N\n"})
        head = r.pull(62, {"MathlibExt/R2.lean": "namespace N\ntheorem S.rec : True := trivial\nend N\n"})
        twin = r.pull(63, {"MathlibExt/R3.lean": "namespace N\ninductive S where | a\nend N\n"})
        self.fetch(61, 62, 63)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": 61, "position": 1, "head": queued}]
        found = self.duplicates(main, entries, head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.rec", "#61")])
        found = self.duplicates(main, entries, twin)["found"]  # the type, not each generated member
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S", "#61")])

    def test_attached_deriving_over_two_lines_collides(self):
        r = self.remote
        queued = r.pull(64, {"MathlibExt/K1.lean": "namespace N\ninductive K\n  | a\n  deriving\n    DecidableEq\nend N\n"})
        head = r.pull(65, {"MathlibExt/K2.lean": "namespace N\ninstance instDecidableEqK : True := trivial\nend N\n"})
        self.fetch(64, 65)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 64, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.instDecidableEqK", "#64")])

    def test_deriving_with_attributes_collides(self):
        r = self.remote
        queued = r.pull(73, {"MathlibExt/E1.lean": "namespace N\ninductive K | a deriving @[expose] DecidableEq\nend N\n"})
        head = r.pull(74, {"MathlibExt/E2.lean": "namespace N\ninstance instDecidableEqK : True := trivial\nend N\n"})
        self.fetch(73, 74)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 73, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.instDecidableEqK", "#73")])

    def test_this_copy_against_mains(self):
        r = self.remote
        main = self.git.rev_parse("refs/preflight/main")
        self.assertIsNone(preflight.copy_differs(self.git, main))  # main has no copy yet
        r.write({preflight.SELF: Path(preflight.__file__).read_text()})
        same = r.commit("Merge pull request #75 from x")
        r.write({preflight.SELF: "# another version\n"})
        other = r.commit("Merge pull request #76 from x")
        self.git.fetch(["+refs/heads/main:refs/preflight/main"])
        self.assertIs(preflight.copy_differs(self.git, same), False)
        self.assertIs(preflight.copy_differs(self.git, other), True)

    def test_duplicates_blame_the_entry_that_adds_the_name(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        edits = r.pull(85, {"MathlibExt/S.lean": "".join(lines[:2] + ["def filler1 := 85\n"] + lines[3:])})
        adds = r.pull(86, {"MathlibExt/S.lean": "".join(lines[:7] + ["def dup := 86\n"] + lines[7:])})
        head = r.pull(87, {"MathlibExt/D5.lean": "namespace Foo\ndef dup := 87\nend Foo\n"})
        self.fetch(85, 86, 87)
        main = self.git.rev_parse("refs/preflight/main")
        entries = [{"number": 85, "position": 1, "head": edits}, {"number": 86, "position": 2, "head": adds}]
        found = self.duplicates(main, entries, head)["found"]
        self.assertEqual([(d["name"], d["source"], d.get("position")) for d in found], [("Foo.dup", "#86", 2)])

    def test_duplicates_blame_main_when_it_added_the_name(self):
        r = self.remote
        ci_base = r.main
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        r.write({"MathlibExt/S.lean": "".join(lines[:7] + ["def dup := 0\n"] + lines[7:])})
        main = r.commit("Merge pull request #94 from x")  # main adds Foo.dup after the CI run
        edits = r.pull(95, {"MathlibExt/S.lean": "".join(lines[:2] + ["def filler1 := 95\n"] + lines[3:7]
                                                         + ["def dup := 0\n"] + lines[7:])}, base=main)
        head = r.pull(96, {"MathlibExt/D6.lean": "namespace Foo\ndef dup := 96\nend Foo\n"}, base=ci_base)
        self.fetch(95, 96)
        found = self.duplicates(main, [{"number": 95, "position": 1, "head": edits}], head, since=ci_base)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("Foo.dup", "main")])

    def test_main_attribution_reads_each_file_once(self):
        r = self.remote
        ci_base = r.main
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        added = [f"def dup{i} := 0\n" for i in range(4)]
        r.write({"MathlibExt/S.lean": "".join(lines[:7] + added + lines[7:])})
        main = r.commit("Merge pull request #107 from x")
        head = r.pull(108, {"MathlibExt/D7.lean": "namespace Foo\n" + "".join(added) + "end Foo\n"}, base=ci_base)
        self.fetch(108)
        with mock.patch.object(self.git, "run", wraps=self.git.run) as run:
            found = self.duplicates(main, [], head, since=ci_base)["found"]
        self.assertEqual(sorted((d["name"], d["source"]) for d in found), [(f"Foo.dup{i}", "main") for i in range(4)])
        lookups = [c for c in run.call_args_list if c.args[:1] == ("rev-parse",) and ":MathlibExt/S.lean" in c.args[-1]]
        self.assertEqual(len(lookups), 2)  # main's and the CI base's copies, once each

    def test_generated_ctor_idx_impl_collides(self):
        r = self.remote
        inductive = r.pull(131, {"MathlibExt/C1.lean": "namespace N\ninductive S where | a | b\nend N\n"})
        impl = r.pull(132, {"MathlibExt/C2.lean": "namespace N\ndef S.ctorIdx._impl : Nat := 0\nend N\n"})
        self.fetch(131, 132)
        main = self.git.rev_parse("refs/preflight/main")
        for queued, number, head in ((inductive, 131, impl), (impl, 132, inductive)):  # both orders
            found = self.duplicates(main, [{"number": number, "position": 1, "head": queued}], head)["found"]
            self.assertEqual([(d["name"], d["source"]) for d in found], [("N.S.ctorIdx._impl", f"#{number}")])

    def test_escaped_names_collide(self):
        r = self.remote
        queued = r.pull(135, {"MathlibExt/E3.lean": "namespace N\ndef «dup» := 1\nend N\n"})
        head = r.pull(136, {"MathlibExt/E4.lean": "namespace «N»\ndef dup := 2\nend «N»\n"})
        self.fetch(135, 136)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 135, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("N.dup", "#135")])  # one Lean name
        self.assertEqual(preflight._canonical("N.«weird name»"), "N.«weird name»")
        self.assertEqual(preflight._canonical("«def»"), "«def»")

    def test_namespace_on_two_lines_collides(self):
        r = self.remote
        queued = r.pull(143, {"MathlibExt/Ns1.lean": "namespace\n  Foo\ndef dup := 1\nend Foo\n"})
        head = r.pull(144, {"MathlibExt/Ns2.lean": "def Foo.dup := 2\n"})
        self.fetch(143, 144)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 143, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("Foo.dup", "#143")])

    def test_structure_fields_collide(self):
        r = self.remote
        queued = r.pull(41, {"MathlibExt/St.lean": "namespace N\nstructure S where\n  x : Nat\nend N\n"})
        head = r.pull(42, {"MathlibExt/Sx.lean": "namespace N.S\ndef x : Nat := 0\nend N.S\n"})
        self.fetch(41, 42)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 41, "position": 1, "head": queued}], head)["found"]
        self.assertEqual([(d["name"], d["source"], d["other_path"]) for d in found],
                         [("N.S.x", "#41", "MathlibExt/St.lean")])

    def test_duplicates_in_libraries_only(self):
        main = self.git.rev_parse("refs/preflight/main")
        result = self.duplicates(main, self.entries[:2], self.head)
        self.assertEqual(result["names"], 1)
        self.assertEqual([(d["name"], d["source"], d["path"], d["other_path"]) for d in result["found"]],
                         [("Foo.dup", "#1", "MathlibExt/C.lean", "MathlibExt/B.lean")])

    def test_renames_and_namespaces_in_the_merge(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        with_shared = "".join(lines[:5] + ["def shared := 2\n"] + lines[5:])
        head = r.pull(15, {"MathlibExt/S.lean": with_shared})
        git(r.path, "checkout", "-q", "--detach", r.main)
        git(r.path, "mv", "MathlibExt/S.lean", "MathlibExt/Renamed.lean")
        r.write({"MathlibExt/Extra.lean": "namespace Foo\ndef shared := 1\nend Foo\n"})
        renamed = r.commit("rename S and add Foo.shared elsewhere")
        git(r.path, "update-ref", "refs/pull/16/head", renamed)
        git(r.path, "checkout", "-q", "main")
        bar = "".join(lines).replace("namespace Foo", "namespace Bar").replace("end Foo", "end Bar")
        renamespaced = r.pull(17, {"MathlibExt/S.lean": bar, "MathlibExt/Extra.lean": "namespace Bar\ndef shared := 1\nend Bar\n"})
        self.fetch(15, 16, 17)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 16, "position": 1, "head": renamed}], head)["found"]
        self.assertEqual([(d["name"], d["path"], d["source"], d["other_path"]) for d in found],
                         [("Foo.shared", "MathlibExt/Renamed.lean", "#16", "MathlibExt/Extra.lean")])
        found = self.duplicates(main, [{"number": 17, "position": 1, "head": renamespaced}], head)["found"]
        self.assertEqual([(d["name"], d["source"], d["other_path"]) for d in found],
                         [("Bar.shared", "#17", "MathlibExt/Extra.lean")])

    def test_anonymous_instances_and_generated_names(self):
        r = self.remote
        queued = r.pull(18, {"MathlibExt/I1.lean": "namespace Foo\ninstance : Inhabited Pt := ⟨⟨0⟩⟩\nend Foo\n"})
        head = r.pull(19, {"MathlibExt/I2.lean": "namespace Foo\ninstance : Inhabited Pt := ⟨⟨1⟩⟩\n"
                                                 "@[simps] def e : Nat ≃ Nat := Equiv.refl _\nend Foo\n"})
        self.fetch(18, 19)
        main = self.git.rev_parse("refs/preflight/main")
        result = self.duplicates(main, [{"number": 18, "position": 1, "head": queued}], head)
        self.assertEqual([(d.get("instance", False), d["name"], d["source"]) for d in result["found"]],
                         [(False, "Foo.instInhabitedPt", "#18")])  # the same approximate name, reported once
        self.assertEqual(result["unpredictable"], ["@[simps] on Foo.e"])
        other = r.pull(20, {"MathlibExt/I3.lean": "namespace Foo\ninstance : Inhabited (Option Pt) := ⟨none⟩\nend Foo\n"})
        self.fetch(20)
        result = self.duplicates(main, [{"number": 20, "position": 1, "head": other}], head)
        self.assertEqual([(d.get("instance", False), d["name"], d["source"]) for d in result["found"]],
                         [(True, "an anonymous Inhabited instance in Foo", "#20")])  # one class, one namespace

    def test_names_that_only_the_merge_creates(self):
        r = self.remote
        r.write({"MathlibExt/Old.lean": "namespace Bar\ndef shared := 0\nend Bar\n"})
        git(r.path, "commit", "-q", "-m", "Merge pull request #21 from x")
        base = git(r.path, "rev-parse", "HEAD")
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        head = r.pull(22, {"MathlibExt/S.lean": "".join(lines[:5] + ["def shared := 2\n"] + lines[5:])}, base=base)
        bar = "".join(lines).replace("namespace Foo", "namespace Bar").replace("end Foo", "end Bar")
        renamespaced = r.pull(23, {"MathlibExt/S.lean": bar}, base=base)
        self.fetch(22, 23)
        result = self.duplicates(base, [{"number": 23, "position": 1, "head": renamespaced}], head)
        self.assertIn("names that its CI did not build (Bar.shared)", result["incomplete"])

    def test_tested_names_come_from_the_ci_merge(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        head = r.pull(30, {"MathlibExt/S.lean": "".join(lines[:5] + ["def shared := 2\n"] + lines[5:])})
        bar = "".join(lines).replace("namespace Foo", "namespace Bar").replace("end Foo", "end Bar")
        r.write({"MathlibExt/S.lean": bar, "MathlibExt/Old.lean": "namespace Foo\ndef shared := 0\nend Foo\n"})
        ci_base = r.commit("Merge pull request #31 from x")  # CI merged the head into this main: Bar.shared
        back = r.pull(32, {"MathlibExt/S.lean": "".join(lines)}, base=ci_base)  # Bar back to Foo
        self.fetch(30, 32)
        alone = self.duplicates(ci_base, [], head, since=ci_base)
        self.assertEqual((alone["found"], alone["incomplete"]), ([], None))  # the tree CI built is fine
        queued = self.duplicates(ci_base, [{"number": 32, "position": 1, "head": back}], head, since=ci_base)
        self.assertIn("names that its CI did not build (Foo.shared)", queued["incomplete"])

    def test_left_out_entries_meet_main_since_ci(self):
        r = self.remote
        ci_base = r.main
        r.write({"MathlibExt/Added.lean": "namespace Foo\ndef shared := 0\nend Foo\n"})
        main = r.commit("Merge pull request #33 from x")
        removes = r.pull(34, {"lakefile.toml": 'name = "removes"\n'}, base=main)
        git(r.path, "checkout", "-q", "--detach", removes)
        git(r.path, "rm", "-q", "MathlibExt/Added.lean")
        removes = r.commit("remove main's copy")
        git(r.path, "update-ref", "refs/pull/34/head", removes)
        git(r.path, "checkout", "-q", "main")
        keeps = r.pull(35, {"lakefile.toml": 'name = "keeps"\n'}, base=main)
        head = r.pull(36, {"MathlibExt/N.lean": "namespace Foo\ndef shared := 1\nend Foo\n"}, base=ci_base)
        self.fetch(34, 35, 36)
        entries = [{"number": 34, "position": 1, "head": removes}, {"number": 35, "position": 2, "head": keeps}]
        found = self.duplicates(main, entries, head, since=ci_base)["found"]
        self.assertEqual([(d["name"], d["source"], d["other_path"]) for d in found],
                         [("Foo.shared", "main", "MathlibExt/Added.lean")])

    def test_names_generated_on_the_other_side(self):
        r = self.remote
        queued = r.pull(24, {"MathlibExt/G1.lean": "namespace Foo\n@[simps] def simpleBox : Nat ≃ Nat := Equiv.refl _\nend Foo\n"})
        head = r.pull(25, {"MathlibExt/G2.lean": "namespace Foo\ntheorem simpleBox_apply : True := trivial\nend Foo\n"})
        self.fetch(24, 25)
        main = self.git.rev_parse("refs/preflight/main")
        result = self.duplicates(main, [{"number": 24, "position": 1, "head": queued}], head)
        self.assertEqual(result["unpredictable"], ["@[simps] on Foo.simpleBox (#24), next to Foo.simpleBox_apply"])

    def test_paired_alias_collides(self):
        r = self.remote
        paired = r.pull(9, {"MathlibExt/P.lean": "namespace Foo\nalias ⟨fwd, bwd⟩ := Iff.rfl\nend Foo\n"})
        head = r.pull(14, {"MathlibExt/Q.lean": "namespace Foo\ntheorem bwd : True := trivial\nend Foo\n"})
        self.fetch(9, 14)
        main = self.git.rev_parse("refs/preflight/main")
        found = self.duplicates(main, [{"number": 9, "position": 1, "head": paired}], head)["found"]
        self.assertEqual([(d["name"], d["source"]) for d in found], [("Foo.bwd", "#9")])
        git(r.path, "merge", "-q", "--no-ff", "-m", "Merge pull request #9 from x", paired)
        merged = git(r.path, "rev-parse", "HEAD")
        self.fetch()
        found = self.duplicates(merged, [], head, since=r.main)["found"]
        self.assertEqual([(d["name"], d["source"], d["main_pr"]) for d in found], [("Foo.bwd", "main", 9)])

    def test_duplicates_in_one_file(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        top = "".join(lines[:2] + ["def shared := 1\n"] + lines[2:])
        bottom = "".join(lines[:-1] + ["def shared := 2\n"] + lines[-1:])
        early = r.pull(4, {"MathlibExt/S.lean": top})
        late = r.pull(11, {"MathlibExt/S.lean": bottom})
        same = r.pull(5, {"MathlibExt/S.lean": bottom})
        self.fetch(4, 5, 11)
        main = self.git.rev_parse("refs/preflight/main")
        twice = self.duplicates(main, [{"number": 4, "position": 1, "head": early}], late)
        self.assertEqual([(d["name"], d["path"], d["other_path"]) for d in twice["found"]],
                         [("Foo.shared", "MathlibExt/S.lean", "MathlibExt/S.lean")])
        once = self.duplicates(main, [{"number": 5, "position": 1, "head": same}], late)
        self.assertEqual(once["found"], [])

    def test_two_moves_of_one_helper(self):
        r = self.remote
        lines = f"namespace Foo\n{FILLER}end Foo\n".splitlines(keepends=True)
        without = "".join(line for line in lines if not line.startswith("def filler3 "))
        moved = "namespace Foo\ndef filler3 := 3\nend Foo\n"
        first = r.pull(8, {"MathlibExt/S.lean": without, "MathlibExt/Y.lean": moved})
        second = r.pull(12, {"MathlibExt/S.lean": without, "MathlibExt/Z.lean": moved})
        alone = r.pull(13, {"MathlibExt/S.lean": without, "MathlibExt/Y.lean": moved})
        self.fetch(8, 12, 13)
        main = self.git.rev_parse("refs/preflight/main")
        both = self.duplicates(main, [{"number": 8, "position": 1, "head": first}], second)
        self.assertEqual([(d["name"], d["path"], d["other_path"]) for d in both["found"]],
                         [("Foo.filler3", "MathlibExt/Z.lean", "MathlibExt/Y.lean")])
        self.assertEqual(self.duplicates(main, [], alone)["found"], [])

    def test_duplicates_on_main_since_the_ci_base(self):
        r = self.remote
        git(r.path, "merge", "-q", "--no-ff", "-m", "Merge pull request #1 from x", self.dup)
        main = git(r.path, "rev-parse", "HEAD")
        self.fetch()
        result = self.duplicates(main, [], self.head, since=r.main)
        self.assertEqual([(d["source"], d["main_pr"]) for d in result["found"]], [("main", 1)])
        self.assertEqual(self.duplicates(main, [], self.head, since=main)["found"], [])
        with mock.patch.object(preflight, "MAX_MAIN_CHANGES", 0):
            self.assertIn("main changed 1 library", self.duplicates(main, [], self.head, since=r.main)["incomplete"])

    @NEEDS_GIT_245
    def test_gather_and_evaluate_end_to_end(self):
        responses, logs = github_6650(self.head)
        pull = responses[f"/repos/{REPO}/pulls/6650"]
        pull.update(mergeable=True, mergeable_state="clean")
        pull["head"]["repo"] = {"full_name": REPO}
        fixture = load("github_6650.json")
        logs[fixture["job_id"]] = logs[fixture["job_id"]].replace("5c77d5224cebd12e0808329f65611358b2a85d9a",
                                                                  self.remote.main)
        gh = FakeGitHub(responses, logs, queue_answer([(1, self.dup), (2, self.bump), (3, self.edit)],
                                                      main=self.remote.main))
        git(self.remote.path, "update-ref", "refs/pull/6650/head", self.head)  # the fake pull request's head
        gh.responses[f"/repos/{REPO}/activity?ref=refs/heads/main&time_period=day"] = []  # a quiet day on main
        read_at = []
        real = preflight.workflow_jobs
        with mock.patch.object(preflight, "workflow_jobs", side_effect=lambda g, c: read_at.append(c) or real(g, c)):
            facts = preflight.gather(gh, self.git, 6650, NOW)
        self.assertEqual(read_at, [facts["main"]])  # the checks and the verdict use one main
        self.assertEqual(facts["reviews"]["codex"]["attested_by"], "pull_request")
        result = preflight.evaluate(facts, NOW)
        failed = {c["name"]: c for c in result["checks"] if not c["ok"]}
        self.assertEqual(result["verdict"], "NOT READY")
        self.assertEqual(set(failed), {"freshness", "conflicts", "duplicates"})
        self.assertIn("#2, queued at position 2, changes lean-toolchain", failed["freshness"]["items"][0])
        self.assertTrue(failed["freshness"]["next"].startswith("wait for #2 to land"))
        self.assertIn("wait for #3 to land", failed["conflicts"]["next"])
        self.assertIn("Foo.dup", failed["duplicates"]["items"][0])
        self.assertEqual(json.loads(json.dumps(result))["verdict"], "NOT READY")


# --------------------------------------------------------------------------------------------------


def ready_facts(**changes) -> dict:
    head = "1" * 40
    facts = {
        "pr": 7000, "repo": REPO, "head": head, "node_id": "PR_x", "title": "t", "state": "open", "draft": False,
        "base": "main", "fork": False, "mergeable": True, "mergeable_state": "clean", "changed_files": 3,
        "queue": {"entries": [{"number": 6999, "position": 1, "head": "2" * 40, "state": "QUEUED"}], "own": None},
        "reviews": {"codex": {"id": 9, "state": "APPROVED", "commit": head, "submitted_at": "2026-11-23T17:00:00Z",
                              "kind": "automatic", "attested_by": "pull_request", "search_incomplete": False},
                    "codex_latest": None, "change_requests": []},
        "checks": {"required": [{"name": n, "status": "completed", "conclusion": "success", "url": None}
                                for n in REQUIRED], "advisory_failed": []},
        "ci": {"run_id": 1, "created_at": "2026-11-23T16:00:00Z", "base": "3" * 40, "base_error": None,
               "main_moved": 30},
        "main": "4" * 40, "files": ["MathlibExt/X.lean"],
        "pins": {"commit": "5" * 40, "pr": 6018, "in_base": True},
        "simulation": {"main": {"clean": True, "files": []}, "entries": [{"number": 6999, "position": 1, "clean": True}],
                       "candidate": {"clean": True, "files": [], "conflicts_with": None}, "pin_changes_ahead": []},
        "duplicates": {"names": 2, "found": [], "incomplete": None},
        "copy_differs": False,
    }
    facts.update(changes)
    return facts


class EvaluateTests(unittest.TestCase):
    def failed(self, facts: dict, **options) -> dict:
        result = preflight.evaluate(facts, NOW, **options)
        return {c["name"]: c for c in result["checks"] if not c["ok"]}

    def test_ready(self):
        result = preflight.evaluate(ready_facts(), NOW)
        self.assertEqual(result["verdict"], "READY")
        self.assertEqual(result["warnings"], [])
        self.assertIn("--enqueue", result["next"])
        self.assertIn("READY", preflight.render(result))

    def test_state(self):
        self.assertIn("draft", self.failed(ready_facts(draft=True))["state"]["detail"])
        queued = preflight.evaluate(ready_facts(queue={"entries": [], "own": {"position": 3, "state": "QUEUED"}},
                                                ci=None), NOW)
        self.assertEqual([c["name"] for c in queued["checks"]], ["state"])
        self.assertIn("do not push", queued["next"])
        self.assertIn("merge main", self.failed(ready_facts(mergeable=False))["state"]["next"])
        self.assertIn("again in a few minutes", self.failed(ready_facts(mergeable=None))["state"]["next"])
        stacked = preflight.evaluate(ready_facts(base="topic"), NOW)
        self.assertIn("land the pull requests below it first", stacked["next"])
        self.assertIn("cannot check a stack", stacked["checks"][0]["detail"])
        closed = preflight.evaluate(ready_facts(state="merged"), NOW)
        self.assertEqual([c["name"] for c in closed["checks"]], ["state"])

    def test_codex(self):
        facts = ready_facts()
        facts["reviews"]["codex"] = None
        facts["reviews"]["codex_latest"] = {"state": "APPROVED", "commit": "9" * 40}
        self.assertIn("@codex", self.failed(facts)["codex"]["next"])
        self.assertIn("ask a maintainer", self.failed(dict(facts, fork=True))["codex"]["next"])
        facts["reviews"]["codex"] = {"state": "CHANGES_REQUESTED", "commit": facts["head"], "submitted_at": "x"}
        self.assertIn("Codex's findings", self.failed(facts)["codex"]["next"])
        facts = ready_facts()
        facts["reviews"]["codex"]["attested_by"] = None
        self.assertIn("no codex-verdict job on the head", self.failed(facts)["codex"]["detail"])
        facts["reviews"]["codex"].update(kind="comment")
        self.assertIn("runs that comments started", self.failed(facts)["codex"]["detail"])
        facts["reviews"]["codex"].update(search_incomplete=True)
        self.assertIn("too many Codex runs", self.failed(facts)["codex"]["detail"])
        facts["reviews"]["codex"].update(attested_by="pull_request_review_comment", search_incomplete=False)
        self.assertNotIn("codex", self.failed(facts))
        changed = ready_facts(files=[".github/workflows/codex.yml"])
        self.assertIn("not on a line of the diff", self.failed(changed)["codex"]["next"])
        changed["reviews"]["codex"].update(kind="comment", attested_by="pull_request_review_comment")
        self.assertIn("codex", self.failed(changed))  # an inline comment runs the changed workflow too
        changed["reviews"]["codex"].update(attested_by="issue_comment")
        self.assertNotIn("codex", self.failed(changed))
        changed["reviews"]["codex"].update(kind="automatic", attested_by="pull_request_target")  # a fork's run
        self.assertNotIn("codex", self.failed(changed))
        facts = ready_facts()
        facts["reviews"]["change_requests"] = [{"login": "someone", "commit": "8" * 40}]
        self.assertIn("someone", self.failed(facts)["codex"]["detail"])

    def test_required_checks(self):
        facts = ready_facts()
        facts["checks"]["required"][1].update(conclusion="failure")
        self.assertIn("build (failure)", self.failed(facts)["required checks"]["detail"])
        facts["checks"]["required"][1].update(conclusion="cancelled")
        self.assertIn("re-run", self.failed(facts)["required checks"]["next"])
        facts["checks"]["required"][1].update(status="in_progress", conclusion=None)
        self.assertIn("Blueprint Pages need no waiting", self.failed(facts)["required checks"]["next"])
        facts = ready_facts()
        facts["checks"]["advisory_failed"] = ["Blueprint Pages"]
        result = preflight.evaluate(facts, NOW)
        self.assertTrue(result["ready"])
        self.assertIn("Blueprint Pages", result["warnings"][0])
        facts = ready_facts()
        facts["checks"]["required"][1].update(conclusion="skipped", scoped=True)  # see scoped_skip
        result = preflight.evaluate(facts, NOW)
        self.assertTrue(result["ready"])
        passed = next(c for c in result["checks"] if c["name"] == "required checks")["detail"]
        self.assertIn("build (skipped: the pull request does not need it)", passed)
        facts["checks"]["required"][0].update(conclusion="skipped")  # any other skip does not pass
        self.assertIn("repository integrity (skipped)", self.failed(facts)["required checks"]["detail"])

    def test_freshness(self):
        facts = ready_facts()
        facts["ci"]["created_at"] = "2026-11-23T11:30:00Z"
        failed = self.failed(facts)["freshness"]
        self.assertIn("6.5 hours ago, more than 6", failed["items"][0])
        self.assertEqual(failed["next"], preflight.REFRESH)
        self.assertNotIn("freshness", self.failed(facts, max_age_hours=7))
        facts = ready_facts()
        facts["pins"]["in_base"] = False
        self.assertIn("predates #6018", self.failed(facts)["freshness"]["items"][0])
        facts = ready_facts()
        facts["ci"].update(base=None, base_error="its log could not be read (HTTP 404)")
        facts["pins"]["in_base"] = None
        failed = self.failed(facts)["freshness"]
        self.assertIn("unknown: its log could not be read", failed["items"][0])
        self.assertIn("once CI has finished", failed["next"])
        facts = ready_facts()
        facts["simulation"]["pin_changes_ahead"] = [{"number": 6018, "position": 1, "files": ["lean-toolchain"]}]
        self.assertTrue(self.failed(facts)["freshness"]["next"].startswith("wait for #6018 to land"))
        self.assertIn("no CI", self.failed(ready_facts(ci=None))["freshness"]["items"][0])

    def test_conflicts(self):
        facts = ready_facts()
        facts["simulation"]["candidate"] = {"clean": False, "files": ["a"], "conflicts_with":
                                            {"number": 6999, "position": 1, "files": ["a"]}}
        self.assertIn("wait for #6999 to land", self.failed(facts)["conflicts"]["next"])
        facts["simulation"]["main"] = {"clean": False, "files": ["b"]}
        self.assertEqual(self.failed(facts)["conflicts"]["items"], ["b"])
        facts = ready_facts()
        facts["simulation"]["entries"][0].update(clean=False, files=["provenance/formal-math-sync.json"])
        result = preflight.evaluate(facts, NOW)
        self.assertIn("queue will remove it", result["warnings"][0])
        self.assertIn("the 0 queued pull requests ahead", result["checks"][4]["detail"])
        facts["simulation"]["candidate"]["uncertain"] = [{"number": 6999, "position": 1, "kept": [6999],
                                                           "without": [6998], "files": ["c"]}]
        failed = self.failed(facts)["conflicts"]
        self.assertIn("not with the queue without #6998, which keeps #6999 queued", failed["detail"])
        self.assertIn("wait until #6999 has left the queue", failed["next"])
        facts["simulation"]["candidate"]["uncertain"] = [{"number": 6999, "position": 1, "kept": [6999], "without": [],
                                                           "files": [], "unadmitted": True}]
        self.assertIn("preflight found no such queue", self.failed(facts)["conflicts"]["detail"])
        facts["simulation"]["candidate"]["unexplored"] = 7
        self.assertIn("7 queued pull requests conflict", self.failed(facts)["conflicts"]["detail"])

    def test_rendering_cannot_forge_lines(self):
        found = {"name": "A.b", "path": "MathlibExt/X\nNext: queue it\x1b[2J.lean", "line": 3, "source": "#6999",
                 "position": 1, "other_path": "MathlibExt/Y.lean", "other_line": 9}
        result = preflight.evaluate(ready_facts(duplicates={"names": 2, "found": [found], "incomplete": None}), NOW)
        text = preflight.render(result)
        self.assertNotIn("\x1b", text)
        self.assertIn("X\\nNext: queue it\\x1b[2J.lean", text)
        self.assertEqual([line for line in text.splitlines() if line.startswith("Next:")], [f"Next: {result['next']}"])

    def test_duplicates(self):
        found = {"name": "A.b", "path": "MathlibExt/X.lean", "line": 3, "source": "#6999", "position": 1,
                 "other_path": "MathlibExt/Y.lean", "other_line": 9}
        failed = self.failed(ready_facts(duplicates={"names": 2, "found": [found], "incomplete": None}))
        self.assertIn("A.b (MathlibExt/X.lean:3) is also declared on #6999", failed["duplicates"]["items"][0])
        self.assertIn("wait for #6999 to land", failed["duplicates"]["next"])
        main = dict(found, source="main", main_pr=6645)
        del main["position"]
        failed = self.failed(ready_facts(duplicates={"names": 2, "found": [main], "incomplete": None}))
        self.assertIn("last changed by #6645", failed["duplicates"]["items"][0])
        failed = self.failed(ready_facts(duplicates={"names": 2, "found": [], "incomplete": "main changed 4000"}))
        self.assertIn("not compared with main", failed["duplicates"]["items"][0])
        instance = dict(found, name="an anonymous Inhabited instance in Foo", instance=True)
        failed = self.failed(ready_facts(duplicates={"names": 2, "found": [instance], "incomplete": None}))
        self.assertIn("may get the same generated name", failed["duplicates"]["items"][0])
        self.assertIn("explicit name", failed["duplicates"]["next"])
        failed = self.failed(ready_facts(duplicates={"names": 2, "found": [], "incomplete": None,
                                                     "unpredictable": ["@[simps] on Foo.e"]}))
        self.assertIn("names that Lean generates for @[simps] on Foo.e", failed["duplicates"]["items"][0])
        self.assertIn("check by hand", failed["duplicates"]["next"])
        alone = preflight.evaluate(ready_facts(duplicates={"names": 2, "found": [], "incomplete": None,
                                                           "unpredictable": ["@[simps] on Foo.e"]}), NOW)
        self.assertTrue(alone["next"].startswith("only hand checks remain"))  # nothing else is wrong
        self.assertIn("queues it from the merge box", alone["next"])

    def test_warnings(self):
        files = ["MathlibExt/Computability/Complexity.lean",
                 "MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes/Basic.lean", "lean-toolchain",
                 ".github/workflows/ci.yml"]
        result = preflight.evaluate(ready_facts(files=files, changed_files=80), NOW)
        self.assertTrue(result["ready"])
        text = "\n".join(result["warnings"])
        for needle in ("about 1,900 modules", "minutes to build", "80 files", "docs/BUMPS.md", "quiet hour",
                       "its own workflows"):
            self.assertIn(needle, text)
        self.assertIn("quiet hour", result["next"])


CODEX_APPROVAL = {"id": 9, "user": {"login": "github-actions[bot]"}, "state": "APPROVED", "commit_id": "1" * 40,
                  "submitted_at": "2026-11-23T17:00:00Z", "body": "<!-- codex-automatic-review -->\n## Codex review"}


def enqueue_github(queue: dict | None = None, reviews: list | None = None) -> FakeGitHub:
    """What enqueue reads again before queueing the pull request of `ready_facts`."""
    return FakeGitHub({f"/repos/{REPO}/pulls/7000": {"state": "open", "draft": False, "head": {"sha": "1" * 40},
                                                     "base": {"ref": "main"}},
                       f"/repos/{REPO}/pulls/7000/reviews": [CODEX_APPROVAL] if reviews is None else reviews},
                      queue=queue or queue_answer([(6999, "2" * 40)]))


class CommandTests(unittest.TestCase):
    def run_main(self, facts: dict, *args: str, queue: dict | None = None,
                 reviews: list | None = None) -> tuple[int, str, FakeGitHub]:
        gh = enqueue_github(queue, reviews)
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as cache, \
                mock.patch.object(preflight, "read_token", return_value="t"), \
                mock.patch.object(preflight, "GitHub", return_value=gh), \
                mock.patch.object(preflight, "gather", return_value=facts), \
                contextlib.redirect_stdout(out):
            status = preflight.main(["7000", "--git-dir", str(Path(cache) / "repo.git"), *args], now=NOW)
        return status, out.getvalue(), gh

    def test_enqueue_only_when_ready(self):
        status, out, gh = self.run_main(ready_facts(), "--enqueue")
        self.assertEqual(status, 0)
        self.assertEqual(gh.mutations, [{"id": "PR_x", "head": "1" * 40, "attempts": 1}])
        self.assertIn("Queued at position 4", out)
        status, out, gh = self.run_main(ready_facts(draft=True), "--enqueue", "--json")
        self.assertEqual(status, 1)
        self.assertEqual(gh.mutations, [])
        self.assertFalse(json.loads(out)["enqueue"]["ok"])

    def test_no_enqueue_when_main_or_the_queue_changed(self):
        for queue, why in [(queue_answer([(6999, "2" * 40), (7001, "3" * 40)]), "the queue changed"),
                           (queue_answer([(6999, "9" * 40)]), "the queue changed"),
                           (queue_answer([]), "the queue changed"),
                           (queue_answer([(6999, "2" * 40)], main="5" * 40), "main moved")]:
            status, out, gh = self.run_main(ready_facts(), "--enqueue", queue=queue)
            self.assertEqual((status, gh.mutations), (1, []))
            self.assertIn(why, out)

    def test_no_enqueue_when_the_reviews_changed(self):
        human = {"id": 10, "user": {"login": "someone"}, "state": "CHANGES_REQUESTED", "commit_id": "1" * 40,
                 "submitted_at": "2026-11-23T17:30:00Z", "body": "wait"}
        for reviews in ([CODEX_APPROVAL, human], [dict(CODEX_APPROVAL, id=11, state="CHANGES_REQUESTED")],
                        [dict(CODEX_APPROVAL, state="DISMISSED")]):
            status, out, gh = self.run_main(ready_facts(), "--enqueue", reviews=reviews)
            self.assertEqual((status, gh.mutations), (1, []))
            self.assertIn("its reviews changed", out)

    def test_no_enqueue_when_the_pull_request_was_retargeted(self):
        gh = enqueue_github()
        gh.responses[f"/repos/{REPO}/pulls/7000"]["base"]["ref"] = "topic"
        result = preflight.enqueue(gh, preflight.evaluate(ready_facts(), NOW))
        self.assertEqual((result["ok"], gh.mutations), (False, []))

    def test_an_ambiguous_enqueue_is_read_back_not_resent(self):
        result = preflight.evaluate(ready_facts(), NOW)
        queued = queue_answer([(6999, "2" * 40), (7000, "1" * 40)], own={"position": 2, "state": "QUEUED"})
        for error, after, ok in [(preflight.Failure("POST /graphql: HTTP 502"), None, False),
                                 (preflight.Failure("POST /graphql: timed out"), queued, True),
                                 (ValueError("Expecting value: line 1 column 1"), queued, True),
                                 (http.client.IncompleteRead(b"{"), queued, True),
                                 (preflight.Failure("timed out"), queue_answer([(6999, "2" * 40), (7000, "9" * 40)],
                                                                             own={"position": 2}), False)]:
            gh = enqueue_github()
            gh.mutation_error, gh.queued_after = error, after
            outcome = preflight.enqueue(gh, result)
            self.assertEqual((outcome["ok"], len(gh.mutations)), (ok, 1))  # one request, never a retry
            if ok:
                self.assertEqual(outcome["position"], 2)
        gh = enqueue_github()
        gh.mutation_answer, gh.queued_after = {"data": {"enqueuePullRequest": None}}, queued
        self.assertTrue(preflight.enqueue(gh, result)["ok"])  # no entry in the answer: read back

    def test_local_errors_exit_2(self):
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp, "file").write_text("")
            err = io.StringIO()
            with mock.patch.object(preflight, "read_token", return_value="t"), \
                    mock.patch.object(preflight, "GitHub", return_value=FakeGitHub({})), \
                    contextlib.redirect_stderr(err):
                status = preflight.main(["7000", "--git-dir", str(Path(tmp, "file", "repo.git"))], now=NOW)
        self.assertEqual(status, 2)
        self.assertIn("preflight:", err.getvalue())

    def test_errors_cannot_forge_lines(self):
        err = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(preflight, "read_token", return_value="t"), \
                mock.patch.object(preflight, "GitHub", return_value=FakeGitHub({})), \
                mock.patch.object(preflight, "gather", side_effect=preflight.Failure("bad\nREADY\x1b[2J")), \
                mock.patch.object(preflight.Git, "ensure"), contextlib.redirect_stderr(err):
            status = preflight.main(["7000", "--git-dir", str(Path(tmp, "repo.git"))], now=NOW)
        self.assertEqual(status, 2)
        self.assertEqual(err.getvalue(), "preflight: bad\\nREADY\\x1b[2J\n")

    def test_a_candidate_that_contains_a_queued_head(self):
        failed = preflight.evaluate(ready_facts(contains_queued=[6999]), NOW)
        self.assertEqual(failed["verdict"], "NOT READY")
        conflicts = next(c for c in failed["checks"] if c["name"] == "conflicts")
        self.assertIn("contains the commits of #6999", conflicts["detail"])
        self.assertIn("wait for #6999 to land", conflicts["next"])

    def test_a_forks_pull_request_is_never_ready(self):
        green = preflight.evaluate(ready_facts(fork=True), NOW)  # even if its runs did name it
        self.assertEqual(green["verdict"], "NOT READY")
        self.assertIn("merge box", green["next"])
        gh = enqueue_github()
        self.assertEqual((preflight.enqueue(gh, green)["ok"], gh.mutations), (False, []))
        unknown = {"name": "build", "status": "unknown", "conclusion": None, "url": None}
        facts = ready_facts(fork=True, checks={"required": [unknown], "advisory_failed": []},
                            ci={"run_id": None, "created_at": None, "base": None,
                                "base_error": "its latest build cannot be tied to this pull request"})
        facts["simulation"]["pin_changes_ahead"] = [{"number": 6018, "position": 1, "files": ["lean-toolchain"]}]
        result = preflight.evaluate(facts, NOW)  # a bump queued ahead is a reason of its own
        self.assertTrue(result["next"].startswith("wait for #6018 to land"))
        self.assertIn("#6018, queued at position 1, changes lean-toolchain",
                      next(c for c in result["checks"] if c["name"] == "freshness")["items"][-1])

    def test_a_change_to_a_workflow_behind_required_checks(self):
        facts = ready_facts(files=[".github/workflows/ci.yml", "MathlibExt/X.lean"],
                            check_workflows=[".github/workflows/bump-guard.yml", ".github/workflows/ci.yml"])
        result = preflight.evaluate(facts, NOW)
        failed = {c["name"]: c for c in result["checks"] if not c["ok"]}
        self.assertEqual(list(failed), ["workflows"])  # its own runs of ci.yml cannot vouch for it
        self.assertIn("the change to .github/workflows/ci.yml", result["next"])
        self.assertTrue(result["next"].startswith("only hand checks remain"))
        gh = enqueue_github()
        self.assertEqual((preflight.enqueue(gh, result)["ok"], gh.mutations), (False, []))

    def test_codex_workflow_changed_by_the_merge(self):
        result = preflight.evaluate(ready_facts(codex_workflow_changed=True), NOW)  # the file list may not show it
        failed = {c["name"]: c for c in result["checks"] if not c["ok"]}
        self.assertIn("codex", failed)
        self.assertIn("used that changed workflow", failed["codex"]["detail"])

    def test_freshness_limits_are_finite(self):
        for args in (["--max-age-hours", "nan"], ["--max-age-hours", "inf"], ["--max-age-hours", "7", "--enqueue"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                preflight.main(["7000", *args], now=NOW)

    def test_one_parse_per_blob_in_the_whole_scan(self):
        pass  # see GitTests.test_duplicate_scan_parses_each_blob_once

    def test_one_parse_per_blob(self):
        texts = {"a" * 40: "def x := 1\n"}
        changes = [(preflight.ZERO_OID, "a" * 40, f"MathlibExt/F{i}.lean") for i in range(50)]
        real = preflight.declarations
        with mock.patch.object(preflight, "declarations", side_effect=real) as parse:
            placed = preflight.placed_declarations(changes, texts)
        self.assertEqual((parse.call_count, len(placed["x"])), (1, 50))
        with mock.patch.object(preflight, "MAX_FILES_READ", 10), self.assertRaises(preflight.Failure):
            preflight.placed_declarations(changes, texts)

    def test_no_enqueue_from_a_copy_that_differs_from_mains(self):
        result = preflight.evaluate(ready_facts(copy_differs=True), NOW)
        self.assertTrue(result["ready"])
        self.assertIn("differs from main's", result["warnings"][0])
        self.assertIn("<main-checkout>/scripts/queue/preflight.py 7000 --enqueue", result["next"])
        for differs, why in ((True, "differs from main's"), (None, "could not be checked against main's")):
            gh = enqueue_github()
            outcome = preflight.enqueue(gh, preflight.evaluate(ready_facts(copy_differs=differs), NOW))
            self.assertEqual((outcome["ok"], gh.mutations), (False, []))
            self.assertIn(why, outcome["error"])

    def test_next_step_names_the_verified_copy(self):
        result = preflight.evaluate(ready_facts(), NOW)
        path = shlex.quote(str(Path(preflight.__file__).resolve()))
        self.assertEqual(result["next"], f"queue it: python3 -I {path} 7000 --enqueue")

    def test_read_only_without_enqueue(self):
        status, out, gh = self.run_main(ready_facts())
        self.assertEqual((status, gh.mutations), (0, []))
        self.assertTrue(out.startswith("#7000 1111111111: READY"))


if __name__ == "__main__":
    unittest.main()
