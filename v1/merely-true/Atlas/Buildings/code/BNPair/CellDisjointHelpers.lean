/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.CellInvProof
import Atlas.Buildings.code.BNPair.CellCoverProof
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace CellDisjoint

open BNPair

/-- Left $B$-absorption: $B \cdot C(w) \subseteq C(w)$. -/
lemma bruhatCell_mul_B_left (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    b * g ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b * b₁, bp.B.mul_mem hb hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, by rw [hg_eq]; group⟩

/-- Right $B$-absorption: $C(w) \cdot B \subseteq C(w)$. -/
lemma bruhatCell_mul_B_right (bp : BNPair G M) {w : M.Group} {g b : G}
    (hg : g ∈ bp.bruhatCell w) (hb : b ∈ bp.B) :
    g * b ∈ bp.bruhatCell w := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

/-- A lift $n \in N$ of a simple reflection $s$ lies in the cell $C(s) = BsB$. -/
lemma N_lift_mem_bruhatCell_simple (bp : BNPair G M) (n : bp.N) (s : B_idx)
    (hn : bp.π n = M.toCoxeterSystem.simple s) :
    (n : G) ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) :=
  ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩

end CellDisjoint
