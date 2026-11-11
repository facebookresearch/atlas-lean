/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Juntas
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.MonotoneFourier
import Atlas.BooleanFunctions.code.Talagrand
import Atlas.BooleanFunctions.code.Theorems

namespace BooleanFourier

open Finset BigOperators

lemma fourierInfluence_eq_influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (i : Fin n) :
    fourierInfluence f i = influenceReal f i := by
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  unfold fourierInfluence
  rw [← Finset.sum_filter]

lemma fourierInfluence_liftPM_eq_influence {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) :
    fourierInfluence (liftPM f) i = influence f i := by
  rw [fourierInfluence_eq_influenceReal]
  have : liftPM f = fun x => boolToReal (f x) := rfl
  rw [this, ← influence_eq_influenceReal]

lemma influence_lt_of_not_mem_highInfluenceCoords {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (i : Fin n) (hi : i ∉ highInfluenceCoords f τ) :
    influence f i < τ := by
  simp only [highInfluenceCoords, Finset.mem_filter, Finset.mem_univ, true_and,
    not_le] at hi
  exact hi

lemma fourierInfluence_lt_of_not_mem_J {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (i : Fin n) (hi : i ∉ highInfluenceCoords f τ) :
    fourierInfluence (liftPM f) i < τ := by
  rw [fourierInfluence_liftPM_eq_influence]
  exact influence_lt_of_not_mem_highInfluenceCoords f τ i hi

theorem fourierCoeff_sq_lt_of_not_subset_J {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (S : Finset (Fin n))
    (hS : ¬(S ⊆ highInfluenceCoords f τ)) :
    fourierCoeff (liftPM f) S ^ 2 < τ := by

  rw [Finset.not_subset] at hS
  obtain ⟨i, hi_S, hi_nJ⟩ := hS
  calc fourierCoeff (liftPM f) S ^ 2
      ≤ fourierInfluence (liftPM f) i :=
        fourierCoeff_sq_le_fourierInfluence (liftPM f) S i hi_S
    _ < τ := fourierInfluence_lt_of_not_mem_J f τ i hi_nJ

lemma log_inv_pos_of_tau {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Real.log (1 / τ) > 0 := by
  rw [Real.log_div (by linarith : (1 : ℝ) ≠ 0) (ne_of_gt hτ0)]
  simp only [Real.log_one, zero_sub]
  exact neg_pos.mpr (Real.log_neg hτ0 hτ1)


lemma fourierCoeff_sq_le_one_of_liftPM {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) :
    fourierCoeff (liftPM f) S ^ 2 ≤ 1 := by
  have hpars : ∑ T : Finset (Fin n), fourierCoeff (liftPM f) T ^ 2 = 1 := by
    have : liftPM f = fun x => boolToReal (f x) := rfl
    rw [this]
    exact parseval_signed f
  have hS_mem : S ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ S
  have h_le := Finset.single_le_sum (f := fun T => fourierCoeff (liftPM f) T ^ 2)
    (fun T _ => sq_nonneg _) hS_mem
  linarith



end BooleanFourier
