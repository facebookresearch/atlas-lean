/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset BigOperators Real

noncomputable section

namespace Rigollet.Chapter5

/-- Sparse hypothesis vector indexed by a binary mask `ω`: places mass `R/k`
on coordinates with `ω i = true` and `0` elsewhere. -/
def sparseVec {d : ℕ} (ω : Fin d → Bool) (R : ℝ) (k : ℝ) : Fin d → ℝ :=
  fun i => if ω i then R / k else 0

/-- `ℓ¹` norm of a sparse hypothesis vector with `k` non-zero coordinates: the
sum of the absolute values equals `R`. -/
theorem l1_norm_sparse {d : ℕ} (ω : Fin d → Bool) (R : ℝ) (k : ℝ)
    (hR : 0 ≤ R) (hk : 0 < k)
    (hcard : ((Finset.univ.filter fun i => ω i = true).card : ℝ) = k) :
    ∑ i : Fin d, |sparseVec ω R k i| = R := by
  have hRk : 0 ≤ R / k := div_nonneg hR hk.le

  have habs : ∀ i : Fin d, |sparseVec ω R k i| = sparseVec ω R k i := by
    intro i; simp only [sparseVec]; split <;> simp [abs_of_nonneg hRk]
  simp_rw [habs, sparseVec]

  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, hcard, mul_div_cancel₀ _ (ne_of_gt hk)]

/-- Squared `ℓ²` norm of a sparse hypothesis vector with `k` non-zero
coordinates equals `R²/k`. -/
theorem l2_sq_sparse {d : ℕ} (ω : Fin d → Bool) (R : ℝ) (k : ℝ)
    (hk : 0 < k)
    (hcard : ((Finset.univ.filter fun i => ω i = true).card : ℝ) = k) :
    ∑ i : Fin d, (sparseVec ω R k i) ^ 2 = R ^ 2 / k := by
  simp only [sparseVec]

  conv_lhs =>
    arg 2; ext i
    rw [show (if ω i = true then R / k else 0) ^ 2 =
        if ω i = true then (R / k) ^ 2 else 0 from by split <;> simp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, hcard]
  rw [div_pow]
  field_simp

/-- Algebraic core of Remark 5.17: if `k ≤ 2/β`, then `β/2 · R² ≤ R²/k`,
yielding the required lower bound on the squared `ℓ²` norm of sparse
hypotheses. -/
theorem remark_5_17_core (k : ℝ) (β : ℝ) (R : ℝ)
    (hk : 0 < k) (hβ : 0 < β) (hkβ : k ≤ 2 / β) :
    β / 2 * R ^ 2 ≤ R ^ 2 / k := by
  rw [le_div_iff₀ hk]
  have h1 : k * β ≤ 2 := by
    have := mul_le_mul_of_nonneg_right hkβ hβ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hβ)] at this
  nlinarith [sq_nonneg R]

end Rigollet.Chapter5

end
