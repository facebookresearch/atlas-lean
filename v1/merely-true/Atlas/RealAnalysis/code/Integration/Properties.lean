/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Set Filter Topology intervalIntegral

namespace Integration

/-- Comparison and triangle inequalities for the Riemann integral.

For continuous functions `f, g : ℝ → ℝ` on `[a, b]` with `a ≤ b`:
1. (Comparison) If `f x ≤ g x` for all `x ∈ [a, b]`, then `∫ x in a..b, f x ≤ ∫ x in a..b, g x`.
2. (Triangle inequality) `|∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|`. -/
theorem integral_comparison_and_triangle (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    ((∀ x ∈ Set.Icc a b, f x ≤ g x) → ∫ x in a..b, f x ≤ ∫ x in a..b, g x) ∧
    (|∫ x in a..b, f x| ≤ ∫ x in a..b, |f x|) := by
  constructor
  · intro hle
    exact intervalIntegral.integral_mono_on hab
      (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable_of_Icc hab) hle
  · have h_norm : ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    simp only [Real.norm_eq_abs] at h_norm
    exact h_norm

/-- Lower and upper bounds for the Riemann integral via the infimum and supremum.

If `f : ℝ → ℝ` is continuous on `[a, b]` with `a ≤ b`, then setting
`m_f = sInf (f '' [a, b])` and `M_f = sSup (f '' [a, b])`, we have
`m_f * (b - a) ≤ ∫ x in a..b, f x ≤ M_f * (b - a)`. -/
theorem integral_bounds (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (sInf (f '' Set.Icc a b)) * (b - a) ≤ ∫ x in a..b, f x ∧
    ∫ x in a..b, f x ≤ (sSup (f '' Set.Icc a b)) * (b - a) := by
  have hint : IntervalIntegrable f volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf
  have hcompact : IsCompact (f '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hf
  have hbdd_above : BddAbove (f '' Set.Icc a b) := hcompact.bddAbove
  have hbdd_below : BddBelow (f '' Set.Icc a b) := hcompact.bddBelow
  constructor
  · calc sInf (f '' Set.Icc a b) * (b - a)
        = ∫ _ in a..b, sInf (f '' Set.Icc a b) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in a..b, f x := by
          apply intervalIntegral.integral_mono_on hab
            intervalIntegral.intervalIntegrable_const hint
          intro x hx
          exact csInf_le hbdd_below (Set.mem_image_of_mem f hx)
  · calc ∫ x in a..b, f x
        ≤ ∫ _ in a..b, sSup (f '' Set.Icc a b) := by
          apply intervalIntegral.integral_mono_on hab hint
            intervalIntegral.intervalIntegrable_const
          intro x hx
          exact le_csSup hbdd_above (Set.mem_image_of_mem f hx)
      _ = sSup (f '' Set.Icc a b) * (b - a) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- Additivity of the Riemann integral over adjacent intervals.

If `f : ℝ → ℝ` is continuous on `[a, b]` and `a < c < b`, then
`∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x`. -/
theorem integral_additivity (f : ℝ → ℝ) (a b c : ℝ) (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x := by
  have hac' : a ≤ c := le_of_lt hac
  have hcb' : c ≤ b := le_of_lt hcb
  have hf_ac : ContinuousOn f (Set.Icc a c) :=
    hf.mono (Set.Icc_subset_Icc_right hcb')
  have hf_cb : ContinuousOn f (Set.Icc c b) :=
    hf.mono (Set.Icc_subset_Icc_left hac')
  have hint_ac : IntervalIntegrable f volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac' hf_ac
  have hint_cb : IntervalIntegrable f volume c b :=
    ContinuousOn.intervalIntegrable_of_Icc hcb' hf_cb
  exact (integral_add_adjacent_intervals hint_ac hint_cb).symm

/-- Linearity of the Riemann integral.

If `f, g : ℝ → ℝ` are continuous on `[a, b]` with `a ≤ b` and `α : ℝ`, then
`∫ x in a..b, (α * f x + g x) = α * (∫ x in a..b, f x) + ∫ x in a..b, g x`. -/
theorem integral_linearity (f g : ℝ → ℝ) (a b α : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (hab : a ≤ b) :
    ∫ x in a..b, (α * f x + g x) = α * (∫ x in a..b, f x) + ∫ x in a..b, g x := by
  have hf_int : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hg_int : IntervalIntegrable g volume a b :=
    hg.intervalIntegrable_of_Icc hab
  have hαf_int : IntervalIntegrable (fun x => α * f x) volume a b :=
    hf_int.const_mul α
  rw [intervalIntegral.integral_add hαf_int hg_int,
      intervalIntegral.integral_const_mul]

end Integration
