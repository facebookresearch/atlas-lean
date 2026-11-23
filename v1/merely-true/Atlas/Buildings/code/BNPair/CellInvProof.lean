/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- *Bruhat cell inversion*: $g \in BwB \;\Rightarrow\; g^{-1} \in Bw^{-1}B$, i.e. $C(w)^{-1} = C(w^{-1})$. -/
theorem BNPair.cell_inv_from_bnpair (bp : BNPair G M)
    (w : M.Group) (g : G) (hg : g ∈ bp.bruhatCell w) :
    g⁻¹ ∈ bp.bruhatCell w⁻¹ := by
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  refine ⟨⟨b₂⁻¹, bp.B.inv_mem hb₂⟩, n⁻¹, ⟨b₁⁻¹, bp.B.inv_mem hb₁⟩, ?_, ?_⟩
  · rw [map_inv, hπ]
  · subst hg_eq; simp; group
