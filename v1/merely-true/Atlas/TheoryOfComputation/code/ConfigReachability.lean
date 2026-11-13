/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.SpaceComplexity

open SpaceComplexity

namespace ConfigReachability

variable {Q : Type} {Γ : Type}

/-- An abstract directed graph whose vertices are configurations: a `Vertex` type with an
adjacency relation `Adj`. The configuration graph `G_{M,w}` of an NTM `M` on input `w` is the
instance with `Vertex = Config Q Γ` and `Adj = M.step`. -/
structure ConfigGraph (Q : Type) (Γ : Type) where
  Vertex : Type
  Adj : Vertex → Vertex → Prop

/-- The configuration graph `G_{M,w}` of NTM `M` on input `w`: vertices are TM configurations
and edges are single steps `M.step`. -/
def mkConfigGraph (M : NTM Q Γ) (_w : List Γ) : ConfigGraph Q Γ where
  Vertex := TuringMachine.Config Q Γ
  Adj := M.step

/-- Reachability in a configuration graph: `Reachable c₁ c₂` is the reflexive–transitive closure
of the adjacency relation. -/
def ConfigGraph.Reachable (G : ConfigGraph Q Γ) (c₁ c₂ : G.Vertex) : Prop :=
  Relation.ReflTransGen G.Adj c₁ c₂

/-- If `branch` is a valid (nondeterministic) computation branch of `M` on input `w`, then for
every step index `k` the configuration `branch k` is reachable from the initial configuration
`M.initConfig w` via `M.step`. -/
lemma branch_reachable_of_valid (M : NTM Q Γ) (w : List Γ)
    (branch : ℕ → TuringMachine.Config Q Γ)
    (hvalid : M.IsValidBranch w branch) (k : ℕ) :
    Relation.ReflTransGen M.step (M.initConfig w) (branch k) := by
  induction k with
  | zero => rw [hvalid.1]
  | succ n ih =>
    have htrans := hvalid.2 n
    by_cases hhalt : M.isHaltConfig (branch n)
    · rw [htrans.2 hhalt]; exact ih
    · exact ih.tail (htrans.1 hhalt)

/-- Converse direction: given a reachability path `a ⟶* b` under `M.step` and the fact that
`b` is a halting configuration, one can extract an actual computation branch `branch : ℕ → Config`
with `branch 0 = a`, `branch k = b`, and the usual NTM branch transition law (steps before
halting, stuttering after halting). -/
lemma exists_branch_of_reflTransGen (M : NTM Q Γ)
    {a b : TuringMachine.Config Q Γ}
    (hreach : Relation.ReflTransGen M.step a b)
    (hhalt_b : M.isHaltConfig b) :
    ∃ (branch : ℕ → TuringMachine.Config Q Γ) (k : ℕ),
      branch 0 = a ∧
      (∀ n, (¬M.isHaltConfig (branch n) → M.step (branch n) (branch (n + 1))) ∧
            (M.isHaltConfig (branch n) → branch (n + 1) = branch n)) ∧
      branch k = b := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>

    exact ⟨fun _ => b, 0, rfl, fun _ => ⟨fun h => absurd hhalt_b h, fun _ => rfl⟩, rfl⟩
  | @head a c hab hcb ih =>


    obtain ⟨branch', k', hstart', htrans', htarget'⟩ := ih

    refine ⟨fun n => match n with | 0 => a | n + 1 => branch' n, k' + 1, rfl, ?_, ?_⟩
    · intro n
      match n with
      | 0 =>
        constructor
        · intro _
          show M.step a (branch' 0)
          rw [hstart']; exact hab
        · intro hhalt_a
          exact absurd hhalt_a hab.1
      | n + 1 => exact htrans' n
    · show branch' k' = b
      exact htarget'

/-- If an accept configuration `c` is reachable from the initial configuration of `M` on `w`
under `M.step`, then `M` accepts `w`. -/
lemma accepts_of_reflTransGen_accept (M : NTM Q Γ) (w : List Γ)
    {c : TuringMachine.Config Q Γ}
    (hreach : Relation.ReflTransGen M.step (M.initConfig w) c)
    (haccept : M.isAcceptConfig c) :
    M.accepts w := by
  have hhalt : M.isHaltConfig c := Or.inl haccept
  obtain ⟨branch, k, hstart, htrans, htarget⟩ :=
    exists_branch_of_reflTransGen M hreach hhalt
  exact ⟨branch, k, ⟨hstart, htrans⟩, htarget ▸ haccept⟩

/-- **Claim (Sipser, Lectures 19/20).** An NTM `M` accepts input `w` if and only if some
accept configuration is reachable from the start configuration `c_start` in the configuration
graph `G_{M,w}`. This is the key bridge between TM acceptance and graph reachability used in
the proofs of `NL ⊆ P` and Savitch's Theorem. -/
theorem accepts_iff_configGraph_reachable
    (M : NTM Q Γ) (w : List Γ) :
    M.accepts w ↔
      ∃ c, M.isAcceptConfig c ∧
        (mkConfigGraph M w).Reachable (M.initConfig w) c := by
  constructor
  ·
    rintro ⟨branch, k, hvalid, haccept⟩
    exact ⟨branch k, haccept, branch_reachable_of_valid M w branch hvalid k⟩
  ·
    rintro ⟨c, haccept, hreach⟩
    exact accepts_of_reflTransGen_accept M w hreach haccept

end ConfigReachability
