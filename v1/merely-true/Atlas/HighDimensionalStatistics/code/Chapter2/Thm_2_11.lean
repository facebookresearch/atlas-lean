/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_10

open Finset BigOperators

namespace HardThresholding

/-- **Theorem 2.11** (properties of hard thresholding under ORT): when the noise is
bounded by `τ` in sup-norm, the hard-thresholding estimator satisfies the oracle
error bound `‖θ̂ − θ*‖² ≤ 16 · |supp θ*| · τ²`, and recovers the true support
provided the nonzero signal entries exceed `3τ` in magnitude. -/
theorem oracle_bound_and_support_recovery {d : ℕ}
    (θstar ξ : Fin d → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hmax : ∀ j : Fin d, |ξ j| ≤ τ) :
    (∑ j : Fin d, (hardThreshold τ (θstar + ξ) j - θstar j) ^ 2 ≤
      16 * ((univ.filter (fun j => θstar j ≠ 0)).card : ℝ) * τ ^ 2)
    ∧
    (∀ (_ : ∀ j, θstar j ≠ 0 → |θstar j| > 3 * τ),
      ∀ j : Fin d, (hardThreshold τ (θstar + ξ) j ≠ 0 ↔ θstar j ≠ 0)) := by
  constructor
  ·
    let S := univ.filter (fun j : Fin d => θstar j ≠ 0)
    let Z := univ.filter (fun j : Fin d => θstar j = 0)
    have huniv : univ = S ∪ Z := by ext x; simp [S, Z]; tauto
    have hdisj : Disjoint S Z := by
      apply Finset.disjoint_filter.mpr; intro x _ h1 h2; exact h1 h2
    have hzero_sum : ∑ j ∈ Z, (hardThreshold τ (θstar + ξ) j - θstar j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hjz : θstar j = 0 := by simpa [Z] using hj
      simp only [hardThreshold, Pi.add_apply, hjz, zero_add, sub_zero]
      have : ¬ (2 * τ < |ξ j|) := by linarith [hmax j]
      simp only [this, ite_false]; norm_num
    have hbound : ∀ j ∈ S, (hardThreshold τ (θstar + ξ) j - θstar j) ^ 2 ≤ 16 * τ ^ 2 := by
      intro j _; have hξ' := abs_le.mp (hmax j)
      simp only [hardThreshold, Pi.add_apply]
      by_cases hy : |θstar j + ξ j| > 2 * τ
      · rw [if_pos hy]; have : (θstar j + ξ j - θstar j) = ξ j := by ring
        rw [this]; nlinarith [sq_abs (ξ j)]
      · rw [if_neg hy]; push Not at hy
        have key' := abs_le.mp (show |θstar j| ≤ 3 * τ by
          calc |θstar j| = |(θstar j + ξ j) + (-ξ j)| := by ring_nf
            _ ≤ |θstar j + ξ j| + |-ξ j| := abs_add_le _ _
            _ = |θstar j + ξ j| + |ξ j| := by rw [abs_neg]
            _ ≤ 2 * τ + τ := by linarith [hmax j]
            _ = 3 * τ := by ring)
        simp only [zero_sub]; rw [neg_sq]
        nlinarith [sq_nonneg (θstar j + 4 * τ), sq_nonneg (θstar j - 4 * τ)]
    calc ∑ j, (hardThreshold τ (θstar + ξ) j - θstar j) ^ 2
        = ∑ j ∈ S, _ + ∑ j ∈ Z, _ := by rw [← Finset.sum_union hdisj, huniv]
      _ = ∑ j ∈ S, _ := by rw [hzero_sum, add_zero]
      _ ≤ ∑ _j ∈ S, (16 * τ ^ 2) := Finset.sum_le_sum hbound
      _ = S.card * (16 * τ ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 16 * (S.card : ℝ) * τ ^ 2 := by ring
  ·
    intro hsig j
    simp only [hardThreshold, Pi.add_apply]; constructor
    · intro h; by_contra heq
      simp only [heq, zero_add] at h; split_ifs at h with habs
      · linarith [hmax j]
      · exact h rfl
    · intro hne
      have key : |θstar j| - |ξ j| ≤ |θstar j + ξ j| := abs_sub_abs_le_abs_add _ _
      have hgt : |θstar j + ξ j| > 2 * τ := by linarith [hsig j hne, hmax j]
      rw [if_pos hgt]; intro h; rw [h] at hgt; simp at hgt; linarith
end HardThresholding
