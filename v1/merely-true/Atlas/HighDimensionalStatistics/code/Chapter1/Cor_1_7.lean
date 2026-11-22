/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3

open MeasureTheory Real ProbabilityTheory BigOperators Finset

/-- **Corollary 1.7 (upper tail).** Let `X₁,…,Xₙ` be independent random
variables, each sub-Gaussian with variance proxy `σ²`. For any coefficients
`a : Fin n → ℝ` and any `t > 0`,
`P(∑ aᵢXᵢ > t) ≤ exp(-t² / (2σ² ∑ aᵢ²))`. -/
theorem corollary_1_7_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {σsq : ℝ}
    (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (a : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, a i * X i ω) > t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) := by

  rcases eq_or_lt_of_le
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)) : (0 : ℝ) ≤ ∑ i, a i ^ 2) with ha | ha
  ·
    have ha0 : ∑ i, a i ^ 2 = 0 := by linarith
    have h_each_zero : ∀ i, a i = 0 := by
      intro i
      have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))
        |>.mp ha0 i (mem_univ i)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
    have h_zero : ∀ ω : Ω, ∑ i, a i * X i ω = 0 := by
      intro ω; apply Finset.sum_eq_zero; intro i _
      rw [h_each_zero i, zero_mul]
    simp_rw [h_zero]
    have : {ω : Ω | (0 : ℝ) > t} = ∅ := by ext ω; simp; linarith
    rw [this]; simp
  ·
    set S := ∑ i, a i ^ 2 with hS_def
    set c := Real.sqrt S with hc_def
    have hc_pos : 0 < c := Real.sqrt_pos_of_pos ha

    set u := fun i => a i / c with hu_def

    have hu_unit : ∑ i, u i ^ 2 = 1 := by
      simp_rw [hu_def, div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt (le_of_lt ha)]
      exact div_self (ne_of_gt ha)

    have hY_sg' := theorem_1_6_subgaussian_vector hX_sg hX_indep hX_meas u
    rw [hu_unit, mul_one] at hY_sg'

    have h_fun_eq : ∀ ω : Ω, ∑ i, a i * X i ω = c * ∑ i, u i * X i ω := by
      intro ω; rw [Finset.mul_sum]; congr 1; ext i
      simp [hu_def]; field_simp

    have h_set_eq : {ω : Ω | (∑ i, a i * X i ω) > t} =
        {ω | (∑ i, u i * X i ω) > t / c} := by
      ext ω; simp only [Set.mem_setOf_eq, h_fun_eq ω, gt_iff_lt]
      constructor
      · intro h; exact (div_lt_iff₀ hc_pos).mpr (by linarith)
      · intro h; linarith [(div_lt_iff₀ hc_pos).mp h]
    rw [h_set_eq]

    have ht_c : 0 < t / c := div_pos ht hc_pos
    calc μ {ω | (∑ i, u i * X i ω) > t / c}
        ≤ ENNReal.ofReal (exp (-((t / c) ^ 2 / (2 * σsq)))) :=
          lemma_1_3_upper_tail hY_sg' (t / c) ht_c
      _ = ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * S)))) := by
          congr 1; congr 1; congr 1
          rw [div_pow, Real.sq_sqrt (le_of_lt ha)]
          ring

/-- **Corollary 1.7 (lower tail).** Symmetric lower-tail version: for
independent sub-Gaussian `X₁,…,Xₙ` with proxy `σ²` and any coefficients
`a : Fin n → ℝ`, `P(∑ aᵢXᵢ < -t) ≤ exp(-t² / (2σ² ∑ aᵢ²))`. -/
theorem corollary_1_7_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {σsq : ℝ}
    (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (a : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, a i * X i ω) < -t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) := by
  rcases eq_or_lt_of_le
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)) : (0 : ℝ) ≤ ∑ i, a i ^ 2) with ha | ha
  ·
    have ha0 : ∑ i, a i ^ 2 = 0 := by linarith
    have h_each_zero : ∀ i, a i = 0 := by
      intro i
      have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))
        |>.mp ha0 i (mem_univ i)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
    have h_zero : ∀ ω : Ω, ∑ i, a i * X i ω = 0 := by
      intro ω; apply Finset.sum_eq_zero; intro i _
      rw [h_each_zero i, zero_mul]
    simp_rw [h_zero]
    have : {ω : Ω | (0 : ℝ) < -t} = ∅ := by ext ω; simp; linarith
    rw [this]; simp
  ·
    set S := ∑ i, a i ^ 2 with hS_def
    set c := Real.sqrt S with hc_def
    have hc_pos : 0 < c := Real.sqrt_pos_of_pos ha
    set u := fun i => a i / c with hu_def
    have hu_unit : ∑ i, u i ^ 2 = 1 := by
      simp_rw [hu_def, div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt (le_of_lt ha)]
      exact div_self (ne_of_gt ha)
    have hY_sg' := theorem_1_6_subgaussian_vector hX_sg hX_indep hX_meas u
    rw [hu_unit, mul_one] at hY_sg'
    have h_fun_eq : ∀ ω : Ω, ∑ i, a i * X i ω = c * ∑ i, u i * X i ω := by
      intro ω; rw [Finset.mul_sum]; congr 1; ext i
      simp [hu_def]; field_simp

    have h_set_eq : {ω : Ω | (∑ i, a i * X i ω) < -t} =
        {ω | (∑ i, u i * X i ω) < -(t / c)} := by
      ext ω; simp only [Set.mem_setOf_eq, h_fun_eq ω]
      rw [show -(t / c) = (-t) / c from by ring]
      rw [lt_div_iff₀ hc_pos]
      constructor <;> intro h <;> linarith [mul_comm c (∑ i, u i * X i ω)]
    rw [h_set_eq]
    have ht_c : 0 < t / c := div_pos ht hc_pos
    calc μ {ω | (∑ i, u i * X i ω) < -(t / c)}
        ≤ ENNReal.ofReal (exp (-((t / c) ^ 2 / (2 * σsq)))) :=
          lemma_1_3_lower_tail hY_sg' (t / c) ht_c
      _ = ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * S)))) := by
          congr 1; congr 1; congr 1
          rw [div_pow, Real.sq_sqrt (le_of_lt ha)]
          ring

/-- **Corollary 1.7 (two-sided form).** Combined upper- and lower-tail bounds
for `∑ aᵢXᵢ` when the `Xᵢ` are independent sub-Gaussian variables with
proxy `σ²`. -/
theorem corollary_1_7_linear_combination_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {σsq : ℝ}
    (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (a : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, a i * X i ω) > t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) ∧
    μ {ω | (∑ i, a i * X i ω) < -t} ≤
      ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq * ∑ i, a i ^ 2)))) :=
  ⟨corollary_1_7_upper_tail hX_sg hX_indep hX_meas a t ht,
   corollary_1_7_lower_tail hX_sg hX_indep hX_meas a t ht⟩
