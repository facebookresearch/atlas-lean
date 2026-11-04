/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectionTheory

/--
Data bundle for the Euclidean projection bound theorem: a scale parameter `R > 1`,
a point set `X` of cardinality `cardX`, a direction set `D` of cardinality `cardD`,
a uniform projection bound `S = max_{θ ∈ D} |π_θ(X)|`, and local covering numbers
`nX r`, `nD ρ` measuring the maximum number of points of `X` (resp. directions of `D`)
in any ball of radius `r` (resp. `ρ`), each bounded above by `cardX`, `cardD`.
-/
structure EuclideanProjectionData where
  R : ℝ
  hR : 1 < R
  cardX : ℕ
  hcardX : 0 < cardX
  cardD : ℕ
  hcardD : 0 < cardD
  S : ℕ
  hS : 0 < S
  nX : ℝ → ℕ
  nD : ℝ → ℕ
  hnX_le : ∀ r, (nX r : ℝ) ≤ cardX
  hnD_le : ∀ ρ, (nD ρ : ℝ) ≤ cardD

/-- Number of dyadic scales `1 ≤ r ≤ R` used in the wave packet decomposition;
explicitly `⌊log₂ ⌈R⌉⌋ + 1`. -/
noncomputable def numDyadicScales (d : EuclideanProjectionData) : ℕ :=
  Nat.log 2 (Nat.ceil d.R) + 1











/-- The number of dyadic scales is at most `log₂ R + 2`, which produces the
logarithmic factor in the final Euclidean projection bound. -/
theorem dyadic_scale_count_le_log (d : EuclideanProjectionData) :
    (numDyadicScales d : ℝ) ≤ Real.logb 2 d.R + 2 := by
  unfold numDyadicScales
  push_cast
  have hR_pos : (0 : ℝ) < d.R := by linarith [d.hR]
  have hceil_pos : 0 < Nat.ceil d.R := Nat.ceil_pos.mpr hR_pos

  have h1 : (Nat.log 2 (Nat.ceil d.R) : ℝ) ≤ Real.logb 2 (Nat.ceil d.R : ℝ) := by
    have := Real.natLog_le_logb (Nat.ceil d.R) 2
    simp only [Nat.cast_ofNat] at this
    exact this

  have h2 : Real.logb 2 (Nat.ceil d.R : ℝ) ≤ Real.logb 2 d.R + 1 := by
    have hceil_bound : (Nat.ceil d.R : ℝ) ≤ 2 * d.R := by
      have h := Nat.ceil_lt_add_one (le_of_lt hR_pos)
      linarith [d.hR]
    calc Real.logb 2 (Nat.ceil d.R : ℝ)
        ≤ Real.logb 2 (2 * d.R) := by
          apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
          · exact Nat.cast_pos.mpr hceil_pos
          · exact hceil_bound
      _ = Real.logb 2 2 + Real.logb 2 d.R := by
          rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hR_pos)]
      _ = 1 + Real.logb 2 d.R := by
          rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      _ = Real.logb 2 d.R + 1 := by ring
  linarith




end ProjectionTheory
