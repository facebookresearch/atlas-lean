/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory Real ProbabilityTheory Set

/-- **Hoeffding's lemma — MGF form (Lemma 1.8).** If `X` is centered and
takes values in `[a,b]` a.s., then for every `s ∈ ℝ`,
`E[exp(sX)] ≤ exp(s² (b-a)² / 8)`. -/
theorem hoeffding_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hab : a < b)
    (hXm : Measurable X)
    (hXa : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hXb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (s : ℝ) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Icc a b :=
    (hXa.and hXb).mono (fun ω ⟨ha, hb⟩ => ⟨ha, hb⟩)
  have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hXm.aemeasurable hIcc hmean
  have hle := hmgf.mgf_le s
  unfold mgf at hle
  simp only at hle
  calc ∫ ω, exp (s * X ω) ∂μ
      ≤ exp (↑((‖b - a‖₊ / 2) ^ 2 : NNReal) * s ^ 2 / 2) := hle
    _ = exp (s ^ 2 * (b - a) ^ 2 / 8) := by
        congr 1
        push_cast
        rw [Real.norm_of_nonneg (sub_nonneg.mpr hab.le)]
        ring

/-- **Hoeffding's lemma (Lemma 1.8).** A centered random variable taking
values in `[a,b]` a.s. is sub-Gaussian with variance proxy `(b-a)²/4`. -/
theorem lemma_1_8_hoeffding {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hab : a < b)
    (hXm : Measurable X)
    (hXi : Integrable X μ)
    (hXa : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hXb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    IsSubGaussian X ((b - a) ^ 2 / 4) μ := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Icc a b :=
    (hXa.and hXb).mono (fun ω ⟨ha, hb⟩ => ⟨ha, hb⟩)
  have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hXm.aemeasurable hIcc hmean
  refine ⟨hXi, hmean, hmgf.integrable_exp_mul, fun s => ?_⟩
  have hle := hmgf.mgf_le s
  unfold mgf at hle
  simp only at hle
  calc ∫ ω, exp (s * X ω) ∂μ
      ≤ exp (↑((‖b - a‖₊ / 2) ^ 2 : NNReal) * s ^ 2 / 2) := hle
    _ = exp ((b - a) ^ 2 / 4 * s ^ 2 / 2) := by
        congr 1
        push_cast
        rw [Real.norm_of_nonneg (sub_nonneg.mpr hab.le)]
        ring
