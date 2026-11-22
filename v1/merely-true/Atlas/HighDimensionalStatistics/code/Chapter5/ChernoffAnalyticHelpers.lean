/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

noncomputable section

namespace ChernoffHelpers


/-- Arithmetic inequality `(n - k + 1)(j + 1) ≤ (n - j)·k` used to drive the
binomial coefficient ratio bound when stepping `j ↦ j + 1`. -/
lemma binom_ratio_ineq (n j k : ℕ) (hj : j + 1 ≤ k) (hk : k ≤ n) :
    (n - k + 1) * (j + 1) ≤ (n - j) * k := by
  have hjn : j ≤ n := le_trans (Nat.le_of_succ_le hj) hk
  zify [hk, hjn]; nlinarith

/-- One-step bound `(n - k + 1)·C(n, j) ≤ k·C(n, j+1)` on consecutive binomial
coefficients, derived from `binom_ratio_ineq`. -/
lemma choose_step_bound (n j k : ℕ) (hj : j + 1 ≤ k) (hk : k ≤ n) :
    (n - k + 1) * Nat.choose n j ≤ k * Nat.choose n (j + 1) := by
  have h := Nat.choose_succ_right_eq n j
  by_cases hcj : Nat.choose n j = 0
  · simp [hcj]
  · have hj1_pos : 0 < j + 1 := Nat.succ_pos j
    suffices (n - k + 1) * Nat.choose n j * (j + 1) ≤
        k * Nat.choose n (j + 1) * (j + 1) from
      Nat.le_of_mul_le_mul_right this hj1_pos
    calc (n - k + 1) * Nat.choose n j * (j + 1)
        = (n - k + 1) * (j + 1) * Nat.choose n j := by ring
      _ ≤ (n - j) * k * Nat.choose n j := by
          apply Nat.mul_le_mul_right; exact binom_ratio_ineq n j k hj hk
      _ = k * (Nat.choose n j * (n - j)) := by ring
      _ = k * (Nat.choose n (j + 1) * (j + 1)) := by rw [h]
      _ = k * Nat.choose n (j + 1) * (j + 1) := by ring

/-- Iterating `choose_step_bound` `m` times yields
`(n - k + 1)^m · C(n, t) ≤ k^m · C(n, t + m)`. -/
lemma choose_iterated_bound (n k t m : ℕ) (htm : t + m ≤ k) (hk : k ≤ n) :
    (n - k + 1) ^ m * Nat.choose n t ≤ k ^ m * Nat.choose n (t + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have htm' : t + m + 1 ≤ k := by omega
    have htm_le : t + m ≤ k := by omega
    have hstep := choose_step_bound n (t + m) k htm' hk
    calc (n - k + 1) ^ (m + 1) * Nat.choose n t
        = (n - k + 1) * ((n - k + 1) ^ m * Nat.choose n t) := by ring
      _ ≤ (n - k + 1) * (k ^ m * Nat.choose n (t + m)) := by
          apply Nat.mul_le_mul_left; exact ih htm_le
      _ = k ^ m * ((n - k + 1) * Nat.choose n (t + m)) := by ring
      _ ≤ k ^ m * (k * Nat.choose n (t + m + 1)) := by
          apply Nat.mul_le_mul_left; exact hstep
      _ = k ^ (m + 1) * Nat.choose n (t + m + 1) := by ring

/-- Specialisation of `choose_iterated_bound` with `m = k - 2t`, giving
`(n - k + 1)^{k - 2t} · C(n, t) ≤ k^{k - 2t} · C(n, k - t)`. -/
lemma choose_ratio_bound (n k t : ℕ) (ht : 2 * t ≤ k) (hk : k ≤ n) :
    (n - k + 1) ^ (k - 2 * t) * Nat.choose n t ≤
      k ^ (k - 2 * t) * Nat.choose n (k - t) := by
  have hm : t + (k - 2 * t) = k - t := by omega
  rw [← hm]
  exact choose_iterated_bound n k t (k - 2 * t) (by omega) hk


/-- Vandermonde decomposition `C(d, k) = ∑_{i+j=k} C(k, i)·C(d - k, j)` used in
the sparse-ball cardinality estimates. -/
lemma vandermonde_decomposition (d k : ℕ) (hk : k ≤ d) :
    Nat.choose d k = ∑ ij ∈ Finset.antidiagonal k,
      Nat.choose k ij.1 * Nat.choose (d - k) ij.2 := by
  have h : d = k + (d - k) := (Nat.add_sub_cancel' hk).symm
  conv_lhs => rw [h]
  exact Nat.add_choose_eq k (d - k) k

/-- Real-analytic inequality `(2(R - 1))^4 ≥ 1 + R` for `R ≥ 4`, fed into the
Chernoff log-ratio estimate. -/
lemma power_ineq_for_chernoff (R : ℝ) (hR : R ≥ 4) :
    (2 * (R - 1)) ^ 4 ≥ 1 + R := by
  nlinarith [sq_nonneg (R - 4), sq_nonneg R, sq_nonneg (R - 1)]

/-- Logarithmic bound `(k/2)·log((d - 2k + 1)/k) ≥ (k/8)·log(1 + d/(2k))`,
the analytic core of the Chernoff sparse-ball estimate. -/
lemma log_ratio_bound (d k : ℝ) (hk : k ≥ 1) (hd : d ≥ 8 * k) :
    k / 2 * Real.log ((d - 2 * k + 1) / k) ≥
      k / 8 * Real.log (1 + d / (2 * k)) := by
  have hk_pos : k > 0 := by linarith
  have hk2_pos : 2 * k > 0 := by linarith
  set R := d / (2 * k) with hR_def
  have hR : R ≥ 4 := by rw [hR_def, ge_iff_le, le_div_iff₀ hk2_pos]; linarith
  have h_ratio_lb : (d - 2 * k + 1) / k ≥ 2 * (R - 1) := by
    rw [ge_iff_le, le_div_iff₀ hk_pos, hR_def]
    have : d / (2 * k) * (2 * k) = d := div_mul_cancel₀ d (ne_of_gt hk2_pos)
    nlinarith
  have h2R1_pos : 2 * (R - 1) > 0 := by linarith
  have h1R_pos : 1 + R > 0 := by linarith
  have hpow : (2 * (R - 1)) ^ 4 ≥ 1 + R := power_ineq_for_chernoff R hR
  have hlog4 : 4 * Real.log (2 * (R - 1)) ≥ Real.log (1 + R) := by
    have : Real.log ((2 * (R - 1)) ^ 4) ≥ Real.log (1 + R) :=
      Real.log_le_log h1R_pos hpow
    rwa [Real.log_pow] at this
  calc k / 2 * Real.log ((d - 2 * k + 1) / k)
      ≥ k / 2 * Real.log (2 * (R - 1)) := by
        apply mul_le_mul_of_nonneg_left (Real.log_le_log h2R1_pos h_ratio_lb)
        linarith
    _ = k / 8 * (4 * Real.log (2 * (R - 1))) := by ring
    _ ≥ k / 8 * Real.log (1 + R) := by
        apply mul_le_mul_of_nonneg_left hlog4; linarith
    _ = k / 8 * Real.log (1 + d / (2 * k)) := by rw [hR_def]

/-- Exponentiated form of `log_ratio_bound`: bounds `exp((k/8)·log(1 + d/(2k)))`
by `((d - 2k + 1)/k)^(k/2)`. -/
lemma exp_le_ratio_pow (d k : ℝ) (hk : k ≥ 1) (hd : d ≥ 8 * k) :
    Real.exp (k / 8 * Real.log (1 + d / (2 * k))) ≤
      ((d - 2 * k + 1) / k) ^ (k / 2) := by
  have h_base_pos : (d - 2 * k + 1) / k > 0 := by apply div_pos <;> linarith
  rw [rpow_def_of_pos h_base_pos]
  apply Real.exp_le_exp.mpr
  rw [mul_comm (Real.log _) _]
  exact log_ratio_bound d k hk hd


/-- Trivial bound `6k ≤ d - 2k + 1` when `d ≥ 8k`. -/
lemma base_ratio_ge_six (d k : ℕ) (_hk : 1 ≤ k) (hd : 8 * k ≤ d) :
    6 * k ≤ d - 2 * k + 1 := by omega

end ChernoffHelpers
