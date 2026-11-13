/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Definitions
import Atlas.BooleanFunctions.code.NoiseStability
import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.Monotone
import Atlas.BooleanFunctions.code.InfluenceFourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Finset BigOperators

namespace BooleanFourier

noncomputable def expect {n : ℕ} (f : BoolFn n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x

noncomputable def variance {n : ℕ} (f : BoolFn n) : ℝ :=
  expect (fun x => f x ^ 2) - (expect f) ^ 2

noncomputable def fourierInfluence {n : ℕ} (f : BoolFn n) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S ^ 2 else 0

lemma fourierCoeff_sq_le_fourierInfluence {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    fourierCoeff f S ^ 2 ≤ fourierInfluence f i := by
  simp only [fourierInfluence]
  calc fourierCoeff f S ^ 2
      = if i ∈ S then fourierCoeff f S ^ 2 else 0 := by simp [hi]
    _ ≤ ∑ T : Finset (Fin n), if i ∈ T then fourierCoeff f T ^ 2 else 0 := by
        apply Finset.single_le_sum
          (f := fun T => if i ∈ T then fourierCoeff f T ^ 2 else 0)
        · intro T _; split_ifs <;> positivity
        · exact Finset.mem_univ S

theorem fourierCoeff_sq_le_avg_fourierInfluence {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    fourierCoeff f S ^ 2 ≤ (1 / (S.card : ℝ)) * ∑ i ∈ S, fourierInfluence f i := by
  have hcard_pos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcard_pos, mul_comm]
  have h : ∀ i ∈ S, fourierCoeff f S ^ 2 ≤ fourierInfluence f i :=
    fun i hi => fourierCoeff_sq_le_fourierInfluence f S i hi
  calc (S.card : ℝ) * fourierCoeff f S ^ 2
      = ∑ _i ∈ S, fourierCoeff f S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ S, fourierInfluence f i := Finset.sum_le_sum h

end BooleanFourier
