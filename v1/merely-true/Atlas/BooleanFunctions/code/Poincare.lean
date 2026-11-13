/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Talagrand
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.Parseval

open Finset BigOperators

namespace BooleanFourier

theorem fourierCoeff_empty_eq_expect {n : ℕ} (f : BoolFn n) :
    fourierCoeff f ∅ = expect f := by
  unfold fourierCoeff expect chi
  simp [Finset.prod_empty]

theorem variance_eq_sum_fourierCoeff_sq_nonempty {n : ℕ} (f : BoolFn n) :
    variance f =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
        (fourierCoeff f S) ^ 2 := by

  have hparseval := parseval f


  have hsplit : ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 =
      (fourierCoeff f ∅) ^ 2 +
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
        (fourierCoeff f S) ^ 2 := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Finset (Fin n)))
      (fun S => S = ∅)
      (fun S => (fourierCoeff f S) ^ 2)
    rw [← h]
    congr 1
    simp [Finset.sum_filter, Finset.sum_ite_eq']

  have hempty : fourierCoeff f ∅ = expect f := fourierCoeff_empty_eq_expect f

  unfold variance
  have hE_sq : expect (fun x => f x ^ 2) = ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 := by
    have : expect (fun x => f x ^ 2) = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x ^ 2 := by
      rfl
    rw [this]
    exact hparseval.symm
  rw [hE_sq, hsplit, hempty]
  ring

theorem poincare_inequality {n : ℕ} (f : BoolFn n) :
    variance f ≤ totalInfluenceReal f := by
  rw [variance_eq_sum_fourierCoeff_sq_nonempty f]
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq f]


  calc ∑ S ∈ Finset.univ.filter (· ≠ ∅), (fourierCoeff f S) ^ 2
      ≤ ∑ S ∈ Finset.univ.filter (· ≠ ∅), (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        rw [Finset.mem_filter] at hS
        have hne : S ≠ ∅ := hS.2
        have hcard : 1 ≤ S.card := Finset.Nonempty.card_pos (Finset.nonempty_of_ne_empty hne)
        have hcard_real : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
        have hsq_nonneg : (0 : ℝ) ≤ (fourierCoeff f S) ^ 2 := sq_nonneg _
        calc (fourierCoeff f S) ^ 2
            = 1 * (fourierCoeff f S) ^ 2 := (one_mul _).symm
          _ ≤ (S.card : ℝ) * (fourierCoeff f S) ^ 2 :=
              mul_le_mul_of_nonneg_right hcard_real hsq_nonneg
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))),
          (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _
        apply mul_nonneg
        · exact_mod_cast Nat.zero_le S.card
        · exact sq_nonneg _
    _ = ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2 := by
        rfl

end BooleanFourier
