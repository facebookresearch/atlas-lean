/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Real Nat

/-- Auxiliary form of Lemma 2.7: `binom(n, k) ≤ (e · n / k)^k` for `1 ≤ k`. -/
theorem lemma_2_7_binom_bound (n k : ℕ) (hk : 1 ≤ k) (_hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hkf_pos : (0 : ℝ) < (k ! : ℝ) := by positivity
  have hkk_pos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hk_pos k

  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k n

  have h2 : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp (k : ℝ) :=
    pow_div_factorial_le_exp (k : ℝ) (le_of_lt hk_pos) k

  have rhs_eq : (Real.exp 1 * ↑n / ↑k) ^ k = Real.exp ↑k * ((↑n) ^ k / (↑k) ^ k) := by
    rw [mul_div_assoc, mul_pow, exp_one_pow, div_pow]
  rw [rhs_eq]

  calc (n.choose k : ℝ)
      ≤ (n : ℝ) ^ k / (k ! : ℝ) := h1
    _ = ((n : ℝ) ^ k / (k : ℝ) ^ k) * ((k : ℝ) ^ k / (k ! : ℝ)) := by field_simp
    _ ≤ ((n : ℝ) ^ k / (k : ℝ) ^ k) * Real.exp (k : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp ↑k * ((↑n) ^ k / (↑k) ^ k) := by ring

/-- **Lemma 2.7**: For `1 ≤ k ≤ n`, `binom(n, k) ≤ (e · n / k)^k`. -/
theorem lemma_2_7 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k :=
  lemma_2_7_binom_bound n k hk hkn
