/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

namespace ConjugatorProof

open BNPair NormalizerParabolic CellCover

/-- **Conjugator-target lemma.** If $g \in G$ conjugates the standard parabolic
$P_{S_1} = BW_{S_1}B$ onto $P_{S_2}$, then $g$ itself lies in $P_{S_2}$.
This is the key step in showing that no two standard parabolics are conjugate in
a BN-pair: any conjugator is forced to land in the target. -/
theorem conjugator_in_target_from_bnpair
    (bp : BNPair G M) (ax : BNPairAxioms bp) :
    ∀ (S₁ S₂ : Set B_idx) (g : G),
    (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ =
      bp.standardParabolic S₂ →
    g ∈ bp.standardParabolic S₂ := by
  intro S₁ S₂ g hconj
  let PS₂ := bp.standardParabolic S₂

  let Q : Subgroup G :=
  { carrier := PS₂
    mul_mem' := fun hx hy => standardParabolic_mul bp ax S₂ hx hy
    one_mem' := B_sub_standardParabolic bp S₂ bp.B.one_mem
    inv_mem' := fun hx => standardParabolic_inv bp S₂ hx }
  have hBQ : bp.B ≤ Q := B_sub_standardParabolic bp S₂


  have hgBg_sub : ∀ b ∈ bp.B, g * b * g⁻¹ ∈ PS₂ := by
    intro b hb
    have hb_PS1 : b ∈ bp.standardParabolic S₁ := B_sub_standardParabolic bp S₁ hb
    have : g * b * g⁻¹ ∈ (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ :=
      ⟨b, hb_PS1, rfl⟩
    rwa [hconj] at this

  obtain ⟨w, hwg⟩ := CellCover.cell_cover_from_bnpair bp ax g

  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hwg


  have hn_conj : ∀ b' ∈ bp.B, (n : G) * b' * (n : G)⁻¹ ∈ (Q : Set G) := by
    intro b' hb'

    have hb'' : (b₂ : G)⁻¹ * b' * b₂ ∈ bp.B :=
      bp.B.mul_mem (bp.B.mul_mem (bp.B.inv_mem hb₂) hb') hb₂

    have hgconj : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ ∈ PS₂ := hgBg_sub _ hb''

    have heq : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ =
        (b₁ : G) * ((n : G) * b' * (n : G)⁻¹) * (b₁ : G)⁻¹ := by
      rw [hg_eq]; group
    rw [heq] at hgconj

    have hb₁_Q : b₁ ∈ (Q : Set G) := hBQ hb₁
    have hb₁_inv_Q : b₁⁻¹ ∈ (Q : Set G) := Q.inv_mem hb₁_Q
    have hgconj_Q : b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹ ∈ (Q : Set G) := hgconj
    have key : (n : G) * b' * (n : G)⁻¹ =
        b₁⁻¹ * (b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹) * b₁ := by group
    rw [key]
    exact Q.mul_mem (Q.mul_mem hb₁_inv_Q hgconj_Q) hb₁_Q

  have hBwB_sub : bp.bruhatCell w ⊆ PS₂ :=
    bruhatCell_sub_of_conj bp ax Q hBQ w n hπ hn_conj

  exact hBwB_sub ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩

end ConjugatorProof
