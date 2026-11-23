/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Basic

open MeasureTheory Set Real Filter Topology

namespace Rigollet.Chapter1

/-- The function `x ↦ -exp(-x²/2)` is an antiderivative of `x ↦ x · exp(-x²/2)`. -/
lemma hasDerivAt_neg_exp_neg_sq_div_two (x : ℝ) :
    HasDerivAt (fun x => -exp (-(x ^ 2 / 2))) (x * exp (-(x ^ 2 / 2))) x := by
  have h1 : HasDerivAt (fun x => -(x ^ 2 / 2)) (-x) x := by
    have h := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
    simp at h
    exact h.neg
  have h2 := h1.exp.neg
  convert h2 using 1
  ring

/-- Limit at `+∞` of the antiderivative `-exp(-x²/2)`, used as a boundary
value when integrating `x · exp(-x²/2)` over `(t, ∞)`. -/
lemma tendsto_neg_exp_neg_sq_div_two :
    Tendsto (fun x : ℝ => -exp (-(x ^ 2 / 2))) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop := by
    apply Filter.Tendsto.atTop_div_const (by positivity : (0 : ℝ) < 2)
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h2 : Tendsto (fun x : ℝ => -(x ^ 2 / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h3 := tendsto_exp_atBot.comp h2
  simp only [Function.comp_def] at h3
  rw [show (0 : ℝ) = -0 from by ring]
  exact h3.neg

/-- Exact value of the improper integral `∫_t^∞ x · exp(-x²/2) dx = exp(-t²/2)`
for `t > 0`. -/
lemma integral_Ioi_x_mul_exp (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi t, x * exp (-(x ^ 2 / 2)) = exp (-(t ^ 2 / 2)) := by
  have hderiv : ∀ x ∈ Ici t,
      HasDerivAt (fun x => -exp (-(x ^ 2 / 2))) (x * exp (-(x ^ 2 / 2))) x :=
    fun x _ => hasDerivAt_neg_exp_neg_sq_div_two x
  have hpos : ∀ x ∈ Ioi t, 0 ≤ x * exp (-(x ^ 2 / 2)) := by
    intro x hx
    exact mul_nonneg (le_of_lt (lt_trans ht hx)) (le_of_lt (exp_pos _))
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos tendsto_neg_exp_neg_sq_div_two]
  simp

/-- The Gaussian density kernel `exp(-x²/2)` is integrable on `(t, ∞)` for
any `t > 0`. -/
lemma integrableOn_exp_neg_sq_div_two (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x => exp (-(x ^ 2 / 2))) (Ioi t) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq
    (by positivity : (0 : ℝ) < 1 / 2) (by norm_num : (-1 : ℝ) < (0 : ℝ))
  simp only [rpow_zero, one_mul] at h
  have h' : IntegrableOn (fun x => exp (-(x ^ 2 / 2))) (Ioi 0) := by
    apply h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    congr 1; ring
  exact h'.mono_set (Ioi_subset_Ioi (le_of_lt ht))

/-- Integrability of `t⁻¹ · x · exp(-x²/2)` on `(t, ∞)`, the upper bound used
in Mills' inequality. -/
lemma integrableOn_inv_t_x_mul_exp (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x => t⁻¹ * (x * exp (-(x ^ 2 / 2)))) (Ioi t) := by
  have hderiv : ∀ x ∈ Ici t,
      HasDerivAt (fun x => -exp (-(x ^ 2 / 2))) (x * exp (-(x ^ 2 / 2))) x :=
    fun x _ => hasDerivAt_neg_exp_neg_sq_div_two x
  have hpos : ∀ x ∈ Ioi t, 0 ≤ x * exp (-(x ^ 2 / 2)) := by
    intro x hx
    exact mul_nonneg (le_of_lt (lt_trans ht hx)) (le_of_lt (exp_pos _))
  exact (integrableOn_Ioi_deriv_of_nonneg' hderiv hpos
    tendsto_neg_exp_neg_sq_div_two).const_mul t⁻¹

/-- **Mills' inequality (analytic form of Proposition 1.1).** For `t > 0`,
`∫_t^∞ exp(-x²/2) dx ≤ t⁻¹ · exp(-t²/2)`. -/
theorem proposition_1_1_mills_inequality (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi t, exp (-(x ^ 2 / 2)) ≤ t⁻¹ * exp (-(t ^ 2 / 2)) := by

  have hpointwise : ∀ x ∈ Ioi t,
      exp (-(x ^ 2 / 2)) ≤ t⁻¹ * (x * exp (-(x ^ 2 / 2))) := by
    intro x hx
    rw [show t⁻¹ * (x * exp (-(x ^ 2 / 2))) = (x / t) * exp (-(x ^ 2 / 2)) by ring]
    have hxt : 1 ≤ x / t := by
      rw [le_div_iff₀ ht]
      linarith [mem_Ioi.mp hx]
    calc exp (-(x ^ 2 / 2))
        = 1 * exp (-(x ^ 2 / 2)) := by ring
      _ ≤ (x / t) * exp (-(x ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hxt (le_of_lt (exp_pos _))

  have hint_lhs := integrableOn_exp_neg_sq_div_two t ht
  have hint_rhs := integrableOn_inv_t_x_mul_exp t ht
  have h_le := setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi hpointwise

  calc ∫ x in Ioi t, exp (-(x ^ 2 / 2))
      ≤ ∫ x in Ioi t, t⁻¹ * (x * exp (-(x ^ 2 / 2))) := h_le
    _ = t⁻¹ * ∫ x in Ioi t, x * exp (-(x ^ 2 / 2)) := integral_const_mul _ _
    _ = t⁻¹ * exp (-(t ^ 2 / 2)) := by rw [integral_Ioi_x_mul_exp t ht]

end Rigollet.Chapter1
