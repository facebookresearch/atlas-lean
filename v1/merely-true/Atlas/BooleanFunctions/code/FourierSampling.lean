/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BooleanFourier

theorem fourierCoeff_eq_expectation {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff f S = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x := by
  rfl

theorem abs_chi_eq_one {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    |chi S x| = 1 := by
  have h := chi_sq S x
  have hne := chi_ne_zero S x
  have habs_sq : |chi S x| ^ 2 = 1 := by
    rw [sq_abs]; exact h
  have habs_nn : (0 : ℝ) ≤ |chi S x| := abs_nonneg _
  nlinarith [sq_nonneg (|chi S x| - 1)]

theorem sample_bounded {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (x : Fin n → Bool) :
    |f x * chi S x| ≤ 1 := by
  rw [abs_mul, abs_chi_eq_one S x, mul_one]
  exact hf x



end BooleanFourier
