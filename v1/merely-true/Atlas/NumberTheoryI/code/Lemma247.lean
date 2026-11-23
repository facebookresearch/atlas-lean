/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open scoped NumberField Classical

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open Subgroup Matrix Finset

variable {K : Type*} [Field K] [NumberField K]

theorem lemma_24_7 (u : InfinitePlace K → (𝓞 K)ˣ)
    (hu : ∀ (v w : InfinitePlace K), w ≠ v → w (u v) < 1) :
    (Subgroup.closure (Set.range u)).FiniteIndex := by
  let u' : Fin (Units.rank K) → (𝓞 K)ˣ := fun i => u ((equivFinRank K i).val)
  have hle : Subgroup.closure (Set.range u') ≤ Subgroup.closure (Set.range u) :=
    Subgroup.closure_mono (fun x ⟨i, hi⟩ => ⟨(equivFinRank K i).val, hi⟩)
  suffices h : (Subgroup.closure (Set.range u')).FiniteIndex from
    Subgroup.finiteIndex_of_le hle
  rw [← isMaxRank_iff_closure_finiteIndex]
  let A : Matrix {w : InfinitePlace K // w ≠ w₀} {w : InfinitePlace K // w ≠ w₀} ℝ :=
    fun v w => logEmbedding K (Additive.ofMul (u v.val)) w
  have hdet : A.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag fun k => by
    have hoff : ∀ j, j ≠ k → A k j < 0 := fun j hjk =>
      show (↑j.val.mult : ℝ) * Real.log (j.val (u k.val)) < 0 from
        mul_neg_of_pos_of_neg (by exact_mod_cast mult_pos)
          (Real.log_neg (Units.pos_at_place (u k.val) j.val)
            (hu k.val j.val (fun h => hjk (Subtype.ext h))))
    have hrowsum : 0 < ∑ j : {w : InfinitePlace K // w ≠ w₀}, A k j := by
      show 0 < ∑ j, (logEmbedding K (Additive.ofMul (u k.val))) j
      rw [sum_logEmbedding_component]
      exact mul_pos_of_neg_of_neg
        (by linarith [show (0 : ℝ) < (w₀ : InfinitePlace K).mult from by exact_mod_cast mult_pos])
        (Real.log_neg (Units.pos_at_place (u k.val) w₀) (hu k.val w₀ (Ne.symm k.prop)))
    simp_rw [Real.norm_eq_abs]
    rw [abs_of_pos (by linarith [Finset.add_sum_erase Finset.univ (fun j => A k j) (Finset.mem_univ k),
        Finset.sum_nonpos (fun j (hj : j ∈ univ.erase k) =>
          le_of_lt (hoff j (Finset.ne_of_mem_erase hj)))])]
    rw [Finset.sum_congr rfl (fun j hj => abs_of_neg (hoff j (Finset.ne_of_mem_erase hj)))]
    rw [Finset.sum_neg_distrib]
    linarith [(Finset.add_sum_erase Finset.univ (fun j => A k j) (Finset.mem_univ k)).symm]
  exact (linearIndependent_equiv (equivFinRank K)).mpr (linearIndependent_rows_of_det_ne_zero hdet)
