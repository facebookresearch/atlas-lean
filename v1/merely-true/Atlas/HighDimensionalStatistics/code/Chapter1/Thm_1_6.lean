/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Real BigOperators Finset

set_option maxHeartbeats 800000

/-- **Theorem 1.6 (Sub-Gaussianity of linear combinations).** Let
`X₁, …, Xₙ` be independent sub-Gaussian random variables with the same
variance proxy `σ²`. Then for any coefficients `a : Fin n → ℝ`, the random
variable `∑ aᵢ Xᵢ` is sub-Gaussian with variance proxy `σ² · ∑ aᵢ²`. -/
theorem theorem_1_6_subgaussian_vector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {σsq : ℝ}
    (hX_sg : ∀ i, IsSubGaussian (X i) σsq μ)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (a : Fin n → ℝ) :
    IsSubGaussian (fun ω => ∑ i, a i * X i ω) (σsq * ∑ i, a i ^ 2) μ := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · exact integrable_finset_sum _ (fun i _ => Integrable.const_mul (hX_sg i).1 (a i))

  · rw [integral_finset_sum _ (fun i _ => Integrable.const_mul (hX_sg i).1 (a i))]
    simp_rw [integral_const_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [(hX_sg i).2.1, mul_zero]

  · intro s
    set Y : Fin n → Ω → ℝ := fun i ω => a i * X i ω with hY_def
    have hY_indep : iIndepFun (β := fun _ : Fin n => ℝ) Y μ :=
      hX_indep.comp (fun i => fun x => a i * x) (fun i => measurable_const.mul measurable_id)
    have hY_meas : ∀ i, Measurable (Y i) := fun i =>
      (measurable_const.mul (hX_meas i))
    have hY_int : ∀ i ∈ Finset.univ, Integrable (fun ω => exp (s * Y i ω)) μ := by
      intro i _
      show Integrable (fun ω => exp (s * (a i * X i ω))) μ
      have : (fun ω => exp (s * (a i * X i ω))) = (fun ω => exp (s * a i * X i ω)) := by
        ext ω; ring_nf
      rw [this]
      exact (hX_sg i).2.2.1 (s * a i)
    have key := hY_indep.integrable_exp_mul_sum hY_meas hY_int
    convert key using 1
    ext ω
    simp only [hY_def, Finset.sum_apply]

  · intro s

    have h_exp_sum : ∫ ω, exp (s * ∑ i, a i * X i ω) ∂μ =
        ∫ ω, ∏ i, exp (s * a i * X i ω) ∂μ := by
      congr 1; ext ω
      rw [mul_sum, exp_sum]
      congr 1; ext i; ring_nf

    have h_indep : ∫ ω, ∏ i, exp (s * a i * X i ω) ∂μ =
        ∏ i, ∫ ω, exp (s * a i * X i ω) ∂μ :=
      hX_indep.integral_fun_prod_comp (𝕜 := ℝ) (f := fun i x => exp (s * a i * x))
        (fun i => (hX_meas i).aemeasurable)
        (fun i => (continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)

    have h_bound : ∏ i, ∫ ω, exp (s * a i * X i ω) ∂μ ≤
        ∏ i, exp (σsq * (s * a i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun ω => le_of_lt (exp_pos _))
      · intro i _
        have h := (hX_sg i).2.2.2 (s * a i)
        simp only [mul_assoc] at h ⊢
        exact h

    have h_simp : ∏ i, exp (σsq * (s * a i) ^ 2 / 2) =
        exp ((σsq * ∑ i, a i ^ 2) * s ^ 2 / 2) := by
      rw [← exp_sum]
      congr 1
      trans (∑ x : Fin n, σsq * a x ^ 2 * s ^ 2 / 2)
      · apply Finset.sum_congr rfl; intro i _; ring
      · rw [← Finset.sum_div, ← Finset.sum_mul, Finset.mul_sum]

    calc ∫ ω, exp (s * ∑ i, a i * X i ω) ∂μ
        = ∫ ω, ∏ i, exp (s * a i * X i ω) ∂μ := h_exp_sum
      _ = ∏ i, ∫ ω, exp (s * a i * X i ω) ∂μ := h_indep
      _ ≤ ∏ i, exp (σsq * (s * a i) ^ 2 / 2) := h_bound
      _ = exp ((σsq * ∑ i, a i ^ 2) * s ^ 2 / 2) := h_simp
