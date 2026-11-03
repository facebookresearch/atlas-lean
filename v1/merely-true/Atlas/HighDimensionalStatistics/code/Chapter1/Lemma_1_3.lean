/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Probability.Moments.Basic

open MeasureTheory Real ProbabilityTheory

namespace SubGaussian

/-- **Lemma 1.3 (Upper tail of a sub-Gaussian variable).** If `X ~ subG(σ²)`,
then `P(X > t) ≤ exp(-t² / (2σ²))` for every `t > 0`. -/
theorem lemma_1_3_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {σsq : ℝ}
    (hX : IsSubGaussian X σsq μ) (t : ℝ) (ht : 0 < t) :
    μ {ω | X ω > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
  rcases le_or_gt σsq 0 with hσ | hσ
  ·
    have h_exp_ge_one : 1 ≤ exp (-(t ^ 2 / (2 * σsq))) := by
      rw [← exp_zero]; apply exp_le_exp.mpr
      rcases eq_or_lt_of_le hσ with h | h
      · subst h; simp
      · exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (by linarith))
    calc μ {ω | X ω > t}
        ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
          ENNReal.ofReal_le_ofReal h_exp_ge_one
  ·
    have h_subset : {ω | X ω > t} ⊆ {ω | t ≤ X ω} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (le_of_lt (exp_pos _))]
    calc (μ {ω | X ω > t}).toReal
        ≤ μ.real {ω | t ≤ X ω} := by
          rw [Measure.real_def]
          exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
      _ ≤ exp (-(t / σsq) * t) * mgf X μ (t / σsq) := by
          apply measure_ge_le_exp_mul_mgf
          · exact le_of_lt (div_pos ht hσ)
          · exact hX.exp_integrable (t / σsq)
      _ ≤ exp (-(t / σsq) * t) * exp (σsq * (t / σsq) ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left
          · simp only [mgf]; exact hX.mgf_bound (t / σsq)
          · exact le_of_lt (exp_pos _)
      _ = exp (-(t ^ 2 / (2 * σsq))) := by
          rw [← exp_add]; congr 1; field_simp; ring

/-- **Lemma 1.3 (Lower tail of a sub-Gaussian variable).** If `X ~ subG(σ²)`,
then `P(X < -t) ≤ exp(-t² / (2σ²))` for every `t > 0`. -/
theorem lemma_1_3_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {σsq : ℝ}
    (hX : IsSubGaussian X σsq μ) (t : ℝ) (ht : 0 < t) :
    μ {ω | X ω < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
  rcases le_or_gt σsq 0 with hσ | hσ
  ·
    have h_exp_ge_one : 1 ≤ exp (-(t ^ 2 / (2 * σsq))) := by
      rw [← exp_zero]; apply exp_le_exp.mpr
      rcases eq_or_lt_of_le hσ with h | h
      · subst h; simp
      · exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (by linarith))
    calc μ {ω | X ω < -t}
        ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
          ENNReal.ofReal_le_ofReal h_exp_ge_one
  ·
    have h_subset : {ω | X ω < -t} ⊆ {ω | X ω ≤ -t} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (le_of_lt (exp_pos _))]
    have hs : -(t / σsq) ≤ 0 := by linarith [div_pos ht hσ]
    calc (μ {ω | X ω < -t}).toReal
        ≤ μ.real {ω | X ω ≤ -t} := by
          rw [Measure.real_def]
          exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
      _ ≤ exp (-(-(t / σsq)) * (-t)) * mgf X μ (-(t / σsq)) := by
          apply measure_le_le_exp_mul_mgf
          · exact hs
          · exact hX.exp_integrable (-(t / σsq))
      _ ≤ exp (-(-(t / σsq)) * (-t)) * exp (σsq * (-(t / σsq)) ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left
          · simp only [mgf]; exact hX.mgf_bound (-(t / σsq))
          · exact le_of_lt (exp_pos _)
      _ = exp (-(t ^ 2 / (2 * σsq))) := by
          rw [← exp_add]; congr 1; field_simp; ring

/-- Combined two-sided tail bounds of Lemma 1.3: for `X ~ subG(σ²)` and any
`t > 0`, both `P(X > t)` and `P(X < -t)` are at most `exp(-t² / (2σ²))`. -/
theorem subGaussian_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {σsq : ℝ}
    (hX : IsSubGaussian X σsq μ) (t : ℝ) (ht : 0 < t) :
    μ {ω | X ω > t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) ∧
    μ {ω | X ω < -t} ≤ ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
  ⟨lemma_1_3_upper_tail hX t ht, lemma_1_3_lower_tail hX t ht⟩

end SubGaussian


export SubGaussian (lemma_1_3_upper_tail lemma_1_3_lower_tail subGaussian_tail_bounds)
