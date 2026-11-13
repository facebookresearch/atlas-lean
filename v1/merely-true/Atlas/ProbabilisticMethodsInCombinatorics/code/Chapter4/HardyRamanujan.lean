/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

set_option maxHeartbeats 400000

open Filter Real Finset

noncomputable section

namespace HardyRamanujan

/-- $\omega(n)$, the number of distinct prime factors of $n$. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card



/-- Chebyshev-type step turning the variance bound into a density bound:
    if $\sum_{x = 1}^N (\omega(x) - \mu)^2 \le C N \mu$, then the proportion of
    $x \in [1, N]$ with $|\omega(x) - \mu| \ge f_N \sqrt{\mu}$ is at most $C / f_N^2$. -/
theorem chebyshev_step {N : ℕ} (hN : 0 < N) {C fN μ : ℝ}
    (hfN : 0 < fN) (hμ : 0 < μ)
    (hVarN : (∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2) ≤ C * (N : ℝ) * μ) :
    ((Finset.filter
        (fun x => fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ|)
        (Finset.Icc 1 N)).card : ℝ) / (N : ℝ) ≤ C / fN ^ 2 := by
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  set S := Finset.filter (fun x => fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ|)
      (Finset.Icc 1 N)

  have h_sq_bound : (S.card : ℝ) * (fN ^ 2 * μ) ≤ C * (N : ℝ) * μ := by
    have h1 : (S.card : ℝ) * (fN * Real.sqrt μ) ^ 2 ≤
        ∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2 := by
      calc (S.card : ℝ) * (fN * Real.sqrt μ) ^ 2
          = ∑ _x ∈ S, (fN * Real.sqrt μ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ S, ((omega x : ℝ) - μ) ^ 2 := by
            apply Finset.sum_le_sum
            intro x hx
            have hxf : fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ| :=
              (Finset.mem_filter.mp hx).2
            nlinarith [sq_abs ((omega x : ℝ) - μ),
              sq_nonneg (|(omega x : ℝ) - μ| - fN * Real.sqrt μ),
              mul_nonneg (le_of_lt hfN) (Real.sqrt_nonneg μ)]
        _ ≤ ∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro x _ _; exact sq_nonneg _
    have h2 : (fN * Real.sqrt μ) ^ 2 = fN ^ 2 * μ := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hμ)]
    linarith [h2 ▸ h1]

  have h_cancel : (S.card : ℝ) * fN ^ 2 ≤ C * (N : ℝ) := by
    nlinarith [h_sq_bound, mul_assoc (S.card : ℝ) (fN ^ 2) μ]

  rw [div_le_div_iff₀ hN' (pow_pos hfN 2)]
  linarith


end HardyRamanujan
