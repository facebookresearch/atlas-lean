/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko

set_option maxHeartbeats 400000

noncomputable section

namespace Sidorenko

/-- A bipartite graph $F$ on $A \sqcup B$ has a "universal vertex" if some vertex in $A$
is adjacent to every vertex of $B$, or some vertex in $B$ is adjacent to every vertex of
$A$. This is the hypothesis of the Conlon-Fox-Sudakov theorem on Sidorenko's conjecture. -/
def HasUniversalVertex {A : Type*} {B : Type*}
    (F : SimpleGraph (A ⊕ B)) : Prop :=
  (∃ a : A, ∀ b : B, F.Adj (Sum.inl a) (Sum.inr b)) ∨
  (∃ b : B, ∀ a : A, F.Adj (Sum.inr b) (Sum.inl a))


/-- A bipartite graph with a universal vertex has at least one edge, so its edge set is
non-empty. Used to avoid degenerate corner cases. -/
theorem hasUniversalVertex_edgeFinset_pos
    {A : Type*} {B : Type*}
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (F : SimpleGraph (A ⊕ B)) [DecidableRel F.Adj]
    (hF : HasUniversalVertex F) :
    0 < F.edgeFinset.card := by
  rcases hF with ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨b⟩ := ‹Nonempty B›
    have hadj := ha b
    have hmem : s(Sum.inl a, Sum.inr b) ∈ F.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  · obtain ⟨a⟩ := ‹Nonempty A›
    have hadj := hb a
    have hmem : s(Sum.inr b, Sum.inl a) ∈ F.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    exact Finset.card_pos.mpr ⟨_, hmem⟩


end Sidorenko
