/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite

namespace SpernerProperty

def IsOrderRaisingLinearMap {α β : Type*} [DecidableEq α]
    (U : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (r : α → β → Prop) : Prop :=
  ∀ (x : α) (y : β), U (Pi.single x 1) y ≠ 0 → r x y

end SpernerProperty

theorem SpernerProperty.order_matching_of_injective_order_raising
    {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
    (r : α → β → Prop)
    (U : (α → ℝ) →ₗ[ℝ] (β → ℝ))
    (hU_inj : Function.Injective U)
    (hU_ord : SpernerProperty.IsOrderRaisingLinearMap U r) :
    ∃ μ : α → β, Function.Injective μ ∧ ∀ x, r x (μ x) := by
  classical
  open Matrix Finset in

  set M := LinearMap.toMatrix' U with hM_def

  have hM_inj : Function.Injective M.mulVec := by
    intro v w h
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec] at h
    exact hU_inj h

  have hLI : LinearIndependent ℝ M.col := by
    rwa [mulVec_injective_iff] at hM_inj


  let t : α → Finset β := fun a => univ.filter (fun b => M b a ≠ 0)

  have hHall : ∀ (S : Finset α), S.card ≤ (S.biUnion t).card := by
    intro S

    have hLI_S : LinearIndependent ℝ (fun (x : ↥S) => M.col ((x : α))) :=
      hLI.comp _ Subtype.val_injective
    set T := S.biUnion t with hT_def


    let restr : (β → ℝ) →ₗ[ℝ] (↥T → ℝ) :=
      { toFun := fun f (t' : ↥T) => f t'
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hLI_restrict : LinearIndependent ℝ (fun (x : ↥S) => restr (M.col (x : α))) := by
      have heq : restr ∘ (fun (x : ↥S) => M.col ((x : α))) =
          fun (x : ↥S) => restr (M.col (x : α)) := rfl
      rw [← heq]
      apply LinearIndependent.map hLI_S
      rw [disjoint_iff, Submodule.eq_bot_iff]
      intro f hf
      rw [Submodule.mem_inf] at hf
      obtain ⟨hf_span, hf_ker⟩ := hf
      rw [LinearMap.mem_ker] at hf_ker
      ext b
      simp only [Pi.zero_apply]
      by_cases hb : b ∈ T
      · exact congr_fun hf_ker ⟨b, hb⟩
      · exact Submodule.span_induction
          (p := fun g _ => g b = 0)
          (fun g hg => by
            simp only [Set.mem_range] at hg
            obtain ⟨⟨a, ha⟩, rfl⟩ := hg
            simp only [col_apply]
            by_contra h
            exact hb (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨mem_univ _, h⟩⟩))
          (by simp)
          (fun _ _ _ _ h1 h2 => by simp [h1, h2])
          (fun c _ _ h1 => by simp [h1])
          hf_span

    calc S.card = Fintype.card ↥S := (Fintype.card_coe S).symm
      _ ≤ Module.finrank ℝ (↥T → ℝ) := hLI_restrict.fintype_card_le_finrank
      _ = Fintype.card ↥T := by
          rw [Module.finrank_pi_fintype, sum_const, smul_eq_mul, Module.finrank_self, mul_one,
              card_univ]
      _ = T.card := Fintype.card_coe T

  rw [all_card_le_biUnion_card_iff_existsInjective'] at hHall
  obtain ⟨f, hf_inj, hf_mem⟩ := hHall

  exact ⟨f, hf_inj, fun x => by
    have hfx := hf_mem x
    simp only [t, mem_filter, mem_univ, true_and] at hfx
    rw [hM_def, LinearMap.toMatrix'_apply] at hfx
    exact hU_ord x (f x) hfx⟩
