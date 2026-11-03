/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Talagrand

open Finset BigOperators Real

namespace BooleanFourier


lemma expect_sq_eq_one {n : ℕ} (f : BoolFn n) (hf : ∀ x, f x = 1 ∨ f x = -1) :
    expect (fun x => f x ^ 2) = 1 := by
  simp only [expect]
  have h_sq : ∀ x, f x ^ 2 = 1 := by
    intro x
    rcases hf x with h | h <;> simp [h]
  simp_rw [h_sq]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool]


lemma fourierInfluence_nonneg {n : ℕ} (f : BoolFn n) (i : Fin n) :
    fourierInfluence f i ≥ 0 := by
  simp only [fourierInfluence]
  apply Finset.sum_nonneg
  intro S _
  split_ifs <;> positivity


lemma variance_le_one {n : ℕ} (f : BoolFn n) (hf : ∀ x, f x = 1 ∨ f x = -1) :
    variance f ≤ 1 := by
  have h1 : expect (fun x => f x ^ 2) = 1 := expect_sq_eq_one f hf
  simp only [variance, h1]
  linarith [sq_nonneg (expect f)]


lemma log_le_two_mul_sqrt {n : ℝ} (hn : 0 < n) : Real.log n ≤ 2 * Real.sqrt n := by
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h := Real.log_le_self hsqrt_nonneg
  rw [Real.log_sqrt hn.le] at h
  linarith




lemma variance_balanced_eq_one {n : ℕ} (f : BoolFn n)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hbal : expect f = 0) :
    variance f = 1 := by
  simp only [variance, expect_sq_eq_one f hf, hbal]
  norm_num



end BooleanFourier
