/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CentralLimitTheorem

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

/-- Density of the standard normal distribution `N(0,1)`:
`φ(x) = (2π)^{-1/2} exp(-x²/2)`. -/
def stdGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The standard normal probability measure on `ℝ`, defined as Lebesgue measure
weighted by the standard Gaussian density `stdGaussianDensity`. -/
def stdNormalMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (stdGaussianDensity x))

/-- A sequence of real random variables `Xₙ : Ω → ℝ` on a measure space `(Ω, P)`
**converges in distribution** to a measure `ν` on `ℝ` if for every bounded
continuous `f : ℝ → ℝ`, `E[f(Xₙ)] → ∫ f dν` (the Portmanteau characterization
of weak convergence). -/
def ConvergesInDistributionRV
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (ν : Measure ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n => ∫ x, f x ∂(P.map (X n))) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Central Limit Theorem.** Let `X₁, X₂, …` be i.i.d. real random variables with
mean `μ` and variance `σ² ∈ (0, ∞)`. Set `Sₙ = X₁ + … + Xₙ`. Then the normalized
sums `(Sₙ − nμ)/(σ √n)` converge in distribution to the standard normal
distribution `N(0, 1)`. -/
theorem central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (μ : ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hmeas : ∀ i, AEMeasurable (X i) P)
    (hmean : ∀ i, ∫ x, X i x ∂P = μ)
    (hvar : ∀ i, ∫ x, (X i x - μ) ^ 2 ∂P = σ ^ 2)
    (hindep : iIndepFun (m := fun _ => inferInstance) X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInDistributionRV
      (fun n ω => (σ * Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - ↑n * μ))
      P stdNormalMeasure := by

  set X' : ℕ → Ω → ℝ := fun k ω => (X k ω - μ) / σ
  have hindep' : iIndepFun (m := fun _ => inferInstance) X' P :=
    hindep.comp (fun _ x => (x - μ) / σ) (fun _ => by fun_prop)
  have hident' : ∀ i, IdentDistrib (X' i) (X' 0) P P := fun i =>
    (hident i).comp (u := fun x => (x - μ) / σ) (by fun_prop)
  have hint0 : Integrable (X 0) P := by
    have hint_sq : Integrable (fun x => (X 0 x - μ) ^ 2) P := by
      by_contra h
      have := integral_undef h
      linarith [hvar 0, sq_pos_of_pos hσ]
    have hL2 : MemLp (fun x => X 0 x - μ) 2 P :=
      (memLp_two_iff_integrable_sq
        ((hmeas 0).sub aemeasurable_const).aestronglyMeasurable).mpr hint_sq
    exact ((hL2.integrable (by norm_num)).add (integrable_const μ)).congr
      (by filter_upwards with ω; simp [sub_add_cancel])

  have h0 : ∫ ω, X' 0 ω ∂P = 0 := by
    simp only [X']
    rw [integral_div, integral_sub hint0 (integrable_const μ), hmean 0, integral_const]
    simp [sub_self]

  have h1 : ∫ ω, (X' 0 ω) ^ 2 ∂P = 1 := by
    simp only [X', div_pow]
    rw [integral_div, hvar 0, div_self (pow_ne_zero 2 (ne_of_gt hσ))]

  have hY : ProbabilityTheory.HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩

  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindep' hident'

  have hTend := hCLT.tendsto
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hTend

  intro f
  have hf := hTend f
  simp only [Measure.map_id] at hf

  have heq_meas : stdNormalMeasure = gaussianReal 0 1 := by
    rw [stdNormalMeasure, gaussianReal_of_var_ne_zero 0 (one_ne_zero)]
    congr 1; funext x
    simp only [stdGaussianDensity, gaussianPDF, gaussianPDFReal]
    norm_cast; congr 1; ring
  rw [heq_meas]

  convert hf using 1
  funext n
  congr 1
  apply Measure.map_congr
  filter_upwards with ω
  simp only [X']
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end
