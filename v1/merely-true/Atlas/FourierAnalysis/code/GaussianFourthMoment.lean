/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace GaussianFourthMoment

lemma hasDerivAt_exp_half_sq (t : ℝ) :
    HasDerivAt (fun t => rexp (t ^ 2 / 2)) (t * rexp (t ^ 2 / 2)) t := by
  have : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const (2 : ℝ); simp at this; exact this
  convert this.exp using 1; ring

lemma hasDerivAt_d1 (t : ℝ) :
    HasDerivAt (fun t => t * rexp (t ^ 2 / 2)) ((1 + t ^ 2) * rexp (t ^ 2 / 2)) t :=
  ((hasDerivAt_id t).mul (hasDerivAt_exp_half_sq t)).congr_deriv (by simp [id]; ring)

lemma hasDerivAt_d2 (t : ℝ) :
    HasDerivAt (fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2))
      ((3 * t + t ^ 3) * rexp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t :=
    ((hasDerivAt_const t 1).add (hasDerivAt_pow 2 t)).congr_deriv (by push_cast; ring)
  exact (h1.mul (hasDerivAt_exp_half_sq t)).congr_deriv (by ring)

lemma hasDerivAt_d3 (t : ℝ) :
    HasDerivAt (fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t :=
    ((hasDerivAt_const t 3).mul (hasDerivAt_id t) |>.add
      (hasDerivAt_pow 3 t)).congr_deriv (by push_cast; ring)
  exact (h1.mul (hasDerivAt_exp_half_sq t)).congr_deriv (by ring)

lemma deriv_four_exp_half_sq_zero :
    deriv (deriv (deriv (deriv (fun (t : ℝ) => rexp (t ^ 2 / 2))))) 0 = 3 := by
  rw [show deriv (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2)
    from funext (fun t => (hasDerivAt_exp_half_sq t).deriv)]
  rw [show deriv (fun t : ℝ => t * rexp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2)
    from funext (fun t => (hasDerivAt_d1 t).deriv)]
  rw [show deriv (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)
    from funext (fun t => (hasDerivAt_d2 t).deriv)]
  rw [show deriv (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2)
    from funext (fun t => (hasDerivAt_d3 t).deriv)]
  simp [exp_zero]

lemma mgf_standard_gaussian :
    mgf id (gaussianReal (0 : ℝ) (1 : ℝ≥0)) = fun t => rexp (t ^ 2 / 2) := by
  ext t
  have h : Measure.map id (gaussianReal (0 : ℝ) (1 : ℝ≥0)) = gaussianReal 0 1 :=
    Measure.map_id
  have hmgf := mgf_gaussianReal h t
  simp at hmgf; exact hmgf

theorem fourth_moment_standard_gaussian :
    ∫ x, x ^ 4 ∂(gaussianReal (0 : ℝ) (1 : ℝ≥0)) = 3 := by
  have h_int : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) (1 : ℝ≥0))) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]; trivial
  have h4 := iteratedDeriv_mgf_zero h_int 4
  simp only [Pi.pow_apply, id_eq] at h4
  rw [← h4, mgf_standard_gaussian]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  exact deriv_four_exp_half_sq_zero

lemma abs_mul_four_le_sum_pow_four (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h1 : a * b * c * d ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
               sq_nonneg (a * b - c * d)]
  have h2 : -(a * b * c * d) ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
               sq_nonneg (a * b + c * d)]
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem product_bound_equidistributed
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Fin 4 → Ω → ℝ)
    (hf_int : ∀ i, Integrable (fun ω => (f i ω) ^ 4) μ)
    (hf_equi : ∀ i, ∫ ω, (f i ω) ^ 4 ∂μ = ∫ ω, (f 0 ω) ^ 4 ∂μ)
    (hf_abs_int : Integrable (fun ω => |f 0 ω * f 1 ω * f 2 ω * f 3 ω|) μ) :
    ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ ≤ ∫ ω, (f 0 ω) ^ 4 ∂μ := by

  have h_sum_int : Integrable
      (fun ω => ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4) μ :=
    (((hf_int 0).add (hf_int 1)).add (hf_int 2) |>.add (hf_int 3)).div_const 4

  have step1 : ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ
      ≤ ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4 ∂μ :=
    integral_mono hf_abs_int h_sum_int
      (fun ω => abs_mul_four_le_sum_pow_four (f 0 ω) (f 1 ω) (f 2 ω) (f 3 ω))

  have step2 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4 ∂μ
      = ∫ ω, (f 0 ω) ^ 4 ∂μ := by
    rw [integral_div]

    have h3 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) ∂μ =
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4) ∂μ + ∫ ω, (f 3 ω) ^ 4 ∂μ :=
      integral_add (((hf_int 0).add (hf_int 1)).add (hf_int 2)) (hf_int 3)
    have h2 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4) ∂μ =
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4) ∂μ + ∫ ω, (f 2 ω) ^ 4 ∂μ :=
      integral_add ((hf_int 0).add (hf_int 1)) (hf_int 2)
    have h1 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4) ∂μ =
        ∫ ω, (f 0 ω) ^ 4 ∂μ + ∫ ω, (f 1 ω) ^ 4 ∂μ :=
      integral_add (hf_int 0) (hf_int 1)
    linarith [hf_equi 1, hf_equi 2, hf_equi 3]
  linarith

theorem gaussian_fourth_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Fin 4 → Ω → ℝ)
    (hf_int : ∀ i, Integrable (fun ω => (f i ω) ^ 4) μ)
    (hf_equi : ∀ i, ∫ ω, (f i ω) ^ 4 ∂μ = ∫ ω, (f 0 ω) ^ 4 ∂μ)
    (hf_abs_int : Integrable (fun ω => |f 0 ω * f 1 ω * f 2 ω * f 3 ω|) μ)
    (hf_gaussian : ∫ ω, (f 0 ω) ^ 4 ∂μ = ∫ x, x ^ 4 ∂(gaussianReal (0 : ℝ) (1 : ℝ≥0))) :
    ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ ≤ 3 := by
  have h_prod := product_bound_equidistributed μ f hf_int hf_equi hf_abs_int
  have h_fourth := fourth_moment_standard_gaussian
  linarith

end GaussianFourthMoment
