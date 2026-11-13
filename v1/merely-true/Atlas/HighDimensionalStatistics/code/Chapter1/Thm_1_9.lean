/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Basic

open MeasureTheory Real ProbabilityTheory BigOperators Finset Set

/-- Mathlib-compatible packaging of Hoeffding's MGF bound: a centered random
variable taking values in `[a,b]` has the `HasSubgaussianMGF` property with
proxy `((b-a)/2)²`. -/
lemma hoeffding_subgaussian_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ} (_hab : a < b)
    (hXm : Measurable X)
    (hXa : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hXb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Icc a b :=
    (hXa.and hXb).mono (fun ω ⟨ha, hb⟩ => ⟨ha, hb⟩)
  exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hXm.aemeasurable hIcc hmean

/-- **Hoeffding's inequality, upper tail for sums.** For independent
centered variables `X_i` with `X_i ∈ [a_i, b_i]` a.s.,
`P(∑ X_i > t) ≤ exp(-2 t² / ∑ (b_i - a_i)²)`. -/
theorem hoeffding_sum_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ)
    (hXa : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω)
    (hXb : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∑ i, X i ω > t} ≤
      ENNReal.ofReal (exp (-(2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) := by

  have hSubG : ∀ i, HasSubgaussianMGF (X i) ((‖b i - a i‖₊ / 2) ^ 2) μ :=
    fun i => hoeffding_subgaussian_mgf (hab i) (hXm i) (hXa i) (hXb i) (hmean i)
  have hMGF : ∀ i s, ∫ ω, exp (s * X i ω) ∂μ ≤ exp (s ^ 2 * (b i - a i) ^ 2 / 8) := by
    intro i s
    have hle := (hSubG i).mgf_le s
    unfold mgf at hle; simp only at hle
    calc ∫ ω, exp (s * X i ω) ∂μ
        ≤ exp (↑((‖b i - a i‖₊ / 2) ^ 2 : NNReal) * s ^ 2 / 2) := hle
      _ = exp (s ^ 2 * (b i - a i) ^ 2 / 8) := by
          congr 1; push_cast
          rw [Real.norm_of_nonneg (sub_nonneg.mpr (hab i).le)]; ring
  have hExpInt : ∀ i s, Integrable (fun ω => exp (s * X i ω)) μ :=
    fun i s => (hSubG i).integrable_exp_mul s

  set D := ∑ i, (b i - a i) ^ 2 with hD_def

  by_cases hn : n = 0
  · subst hn; simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have : {ω : Ω | (0 : ℝ) > t} = ∅ := by ext ω; simp; linarith
    rw [this]; simp

  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hD_pos : 0 < D := by
    apply Finset.sum_pos
    · intro i _; exact sq_pos_of_pos (sub_pos.mpr (hab i))
    · exact Finset.univ_nonempty

  set s_opt := 4 * t / D with hs_opt_def
  have hs_pos : 0 < s_opt := div_pos (by linarith) hD_pos

  have h_subset : {ω : Ω | ∑ i, X i ω > t} ⊆ {ω | t ≤ ∑ i, X i ω} := by
    intro ω hω; simp only [mem_setOf_eq] at hω ⊢; linarith

  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (le_of_lt (exp_pos _))]
  have h_toReal_le : (μ {ω | ∑ i, X i ω > t}).toReal ≤ μ.real {ω | t ≤ ∑ i, X i ω} := by
    rw [Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)

  have h_sum_int : Integrable (fun ω => exp (s_opt * ∑ i, X i ω)) μ := by
    have h_eq : (fun ω => exp (s_opt * ∑ i, X i ω)) =
        (fun ω => exp (s_opt * (∑ i, X i) ω)) := by
      ext ω; simp [Finset.sum_apply]
    rw [h_eq]
    exact hX_indep.integrable_exp_mul_sum hXm (fun i _ => hExpInt i s_opt)

  have h_chernoff := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω)
    t (le_of_lt hs_pos) h_sum_int

  have h_mgf_eq : mgf (fun ω => ∑ i, X i ω) μ s_opt =
      ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ := by
    unfold mgf; simp only
    have h_eq : (fun ω : Ω => exp (s_opt * ∑ i, X i ω)) =
        (fun ω => ∏ i, exp (s_opt * X i ω)) := by
      ext ω; rw [mul_sum, exp_sum]
    rw [h_eq]
    have key := hX_indep.integral_fun_prod_comp
      (f := fun i x => exp (s_opt * x))
      (fun i => (hXm i).aemeasurable)
      (fun i => Continuous.aestronglyMeasurable
        (continuous_exp.comp (continuous_const.mul continuous_id)))
    convert key using 1

  have h_prod_bound : ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ ≤
      ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) := by
    apply Finset.prod_le_prod
    · intro i _; exact integral_nonneg (fun ω => le_of_lt (exp_pos _))
    · intro i _; exact hMGF i s_opt

  have h_prod_exp : ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) =
      exp (s_opt ^ 2 / 8 * D) := by
    rw [← exp_sum]; congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

  calc (μ {ω | ∑ i, X i ω > t}).toReal
      ≤ μ.real {ω | t ≤ ∑ i, X i ω} := h_toReal_le
    _ ≤ exp (-s_opt * t) * mgf (fun ω => ∑ i, X i ω) μ s_opt := h_chernoff
    _ = exp (-s_opt * t) * ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ := by rw [h_mgf_eq]
    _ ≤ exp (-s_opt * t) * ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left h_prod_bound (le_of_lt (exp_pos _))
    _ = exp (-s_opt * t) * exp (s_opt ^ 2 / 8 * D) := by rw [h_prod_exp]
    _ = exp (-s_opt * t + s_opt ^ 2 / 8 * D) := by rw [← exp_add]
    _ = exp (-(2 * t ^ 2 / D)) := by
        congr 1; rw [hs_opt_def]; field_simp; ring

/-- **Hoeffding's inequality, lower tail for sums.** Under the same hypotheses
as the upper-tail version, `P(∑ X_i < -t) ≤ exp(-2 t² / ∑ (b_i - a_i)²)`. -/
theorem hoeffding_sum_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ)
    (hXa : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω)
    (hXb : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∑ i, X i ω < -t} ≤
      ENNReal.ofReal (exp (-(2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) := by

  have hSubG : ∀ i, HasSubgaussianMGF (X i) ((‖b i - a i‖₊ / 2) ^ 2) μ :=
    fun i => hoeffding_subgaussian_mgf (hab i) (hXm i) (hXa i) (hXb i) (hmean i)
  have hMGF : ∀ i s, ∫ ω, exp (s * X i ω) ∂μ ≤ exp (s ^ 2 * (b i - a i) ^ 2 / 8) := by
    intro i s
    have hle := (hSubG i).mgf_le s
    unfold mgf at hle; simp only at hle
    calc ∫ ω, exp (s * X i ω) ∂μ
        ≤ exp (↑((‖b i - a i‖₊ / 2) ^ 2 : NNReal) * s ^ 2 / 2) := hle
      _ = exp (s ^ 2 * (b i - a i) ^ 2 / 8) := by
          congr 1; push_cast
          rw [Real.norm_of_nonneg (sub_nonneg.mpr (hab i).le)]; ring
  have hExpInt : ∀ i s, Integrable (fun ω => exp (s * X i ω)) μ :=
    fun i s => (hSubG i).integrable_exp_mul s
  set D := ∑ i, (b i - a i) ^ 2 with hD_def
  by_cases hn : n = 0
  · subst hn; simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have : {ω : Ω | (0 : ℝ) < -t} = ∅ := by ext ω; simp; linarith
    rw [this]; simp
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hD_pos : 0 < D := by
    apply Finset.sum_pos
    · intro i _; exact sq_pos_of_pos (sub_pos.mpr (hab i))
    · exact Finset.univ_nonempty

  set s_opt := -(4 * t / D) with hs_opt_def
  have hs_neg : s_opt ≤ 0 := by
    rw [hs_opt_def]; linarith [div_pos (by linarith : 0 < 4 * t) hD_pos]
  have h_subset : {ω : Ω | ∑ i, X i ω < -t} ⊆ {ω | ∑ i, X i ω ≤ -t} := by
    intro ω hω; simp only [mem_setOf_eq] at hω ⊢; linarith
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (le_of_lt (exp_pos _))]
  have h_toReal_le : (μ {ω | ∑ i, X i ω < -t}).toReal ≤ μ.real {ω | ∑ i, X i ω ≤ -t} := by
    rw [Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
  have h_sum_int : Integrable (fun ω => exp (s_opt * ∑ i, X i ω)) μ := by
    have h_eq : (fun ω => exp (s_opt * ∑ i, X i ω)) =
        (fun ω => exp (s_opt * (∑ i, X i) ω)) := by
      ext ω; simp [Finset.sum_apply]
    rw [h_eq]
    exact hX_indep.integrable_exp_mul_sum hXm (fun i _ => hExpInt i s_opt)

  have h_chernoff := measure_le_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω)
    (-t) hs_neg h_sum_int

  have h_mgf_eq : mgf (fun ω => ∑ i, X i ω) μ s_opt =
      ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ := by
    unfold mgf; simp only
    have h_eq : (fun ω : Ω => exp (s_opt * ∑ i, X i ω)) =
        (fun ω => ∏ i, exp (s_opt * X i ω)) := by
      ext ω; rw [mul_sum, exp_sum]
    rw [h_eq]
    have key := hX_indep.integral_fun_prod_comp
      (f := fun i x => exp (s_opt * x))
      (fun i => (hXm i).aemeasurable)
      (fun i => Continuous.aestronglyMeasurable
        (continuous_exp.comp (continuous_const.mul continuous_id)))
    convert key using 1
  have h_prod_bound : ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ ≤
      ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) := by
    apply Finset.prod_le_prod
    · intro i _; exact integral_nonneg (fun ω => le_of_lt (exp_pos _))
    · intro i _; exact hMGF i s_opt
  have h_prod_exp : ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) =
      exp (s_opt ^ 2 / 8 * D) := by
    rw [← exp_sum]; congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  calc (μ {ω | ∑ i, X i ω < -t}).toReal
      ≤ μ.real {ω | ∑ i, X i ω ≤ -t} := h_toReal_le
    _ ≤ exp (-s_opt * (-t)) * mgf (fun ω => ∑ i, X i ω) μ s_opt := h_chernoff
    _ = exp (-s_opt * (-t)) * ∏ i, ∫ ω, exp (s_opt * X i ω) ∂μ := by rw [h_mgf_eq]
    _ ≤ exp (-s_opt * (-t)) * ∏ i, exp (s_opt ^ 2 * (b i - a i) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left h_prod_bound (le_of_lt (exp_pos _))
    _ = exp (-s_opt * (-t)) * exp (s_opt ^ 2 / 8 * D) := by rw [h_prod_exp]
    _ = exp (-s_opt * (-t) + s_opt ^ 2 / 8 * D) := by rw [← exp_add]
    _ = exp (-(2 * t ^ 2 / D)) := by
        congr 1; rw [hs_opt_def]; field_simp; ring

/-- **Hoeffding's inequality for the sample mean — upper tail.** For
independent `X_i ∈ [a_i, b_i]`,
`P((1/n)∑(X_i - E X_i) > t) ≤ exp(-2 n² t² / ∑ (b_i - a_i)²)`. -/
theorem hoeffding_sample_mean_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ)
    (hXa : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω)
    (hXb : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b i)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n > t} ≤
      ENNReal.ofReal (exp (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) := by

  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂μ with hY_def

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_set_eq : {ω : Ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n > t}
      = {ω | ∑ i, Y i ω > ↑n * t} := by
    ext ω; simp only [mem_setOf_eq, hY_def, Finset.sum_sub_distrib]
    constructor <;> intro h
    · rw [show (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n =
            (∑ i, X i ω - ∑ i, ∫ ω', X i ω' ∂μ) / ↑n from by field_simp] at h
      rwa [gt_iff_lt, lt_div_iff₀ hn_pos, mul_comm] at h
    · rw [show (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n =
            (∑ i, X i ω - ∑ i, ∫ ω', X i ω' ∂μ) / ↑n from by field_simp,
        gt_iff_lt, lt_div_iff₀ hn_pos, mul_comm]; exact h
  rw [h_set_eq]

  rw [show (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) : ℝ)
      = -(2 * (↑n * t) ^ 2 / ∑ i, (b i - a i) ^ 2) from by ring]

  have hY_indep : iIndepFun (β := fun _ : Fin n => ℝ) Y μ := by
    rw [hY_def]
    exact hX_indep.comp (fun i => fun x => x - ∫ ω', X i ω' ∂μ)
      (fun i => measurable_sub_const _)
  have hYm : ∀ i, Measurable (Y i) := fun i => (hXm i).sub measurable_const
  have hYi : ∀ i, Integrable (Y i) μ := fun i => (hXi i).sub (integrable_const _)
  have hYa : ∀ i, ∀ᵐ ω ∂μ, (a i - ∫ ω', X i ω' ∂μ) ≤ Y i ω := by
    intro i; filter_upwards [hXa i] with ω hω; simp [hY_def]; linarith
  have hYb : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ (b i - ∫ ω', X i ω' ∂μ) := by
    intro i; filter_upwards [hXb i] with ω hω; simp [hY_def]; linarith
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i; simp [hY_def]
    rw [integral_sub (hXi i) (integrable_const _)]; simp [integral_const]
  have hab' : ∀ i, (a i - ∫ ω', X i ω' ∂μ) < (b i - ∫ ω', X i ω' ∂μ) :=
    fun i => sub_lt_sub_right (hab i) _

  have h_range_eq : (∑ i, ((b i - ∫ ω', X i ω' ∂μ) - (a i - ∫ ω', X i ω' ∂μ)) ^ 2)
      = ∑ i, (b i - a i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; ring_nf
  rw [← h_range_eq]
  exact hoeffding_sum_upper_tail hab' hYm hYi hYa hYb hYmean hY_indep
    (↑n * t) (mul_pos hn_pos ht)

/-- **Hoeffding's inequality for the sample mean — lower tail.** Symmetric
counterpart of the upper-tail bound for the centered sample mean. -/
theorem hoeffding_sample_mean_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ)
    (hXa : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω)
    (hXb : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b i)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n < -t} ≤
      ENNReal.ofReal (exp (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) := by
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂μ with hY_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_set_eq : {ω : Ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n < -t}
      = {ω | ∑ i, Y i ω < -(↑n * t)} := by
    ext ω; simp only [mem_setOf_eq, hY_def, Finset.sum_sub_distrib]
    constructor <;> intro h
    · rw [show (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n =
            (∑ i, X i ω - ∑ i, ∫ ω', X i ω' ∂μ) / ↑n from by field_simp] at h
      rw [div_lt_iff₀ hn_pos] at h; linarith
    · rw [show (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n =
            (∑ i, X i ω - ∑ i, ∫ ω', X i ω' ∂μ) / ↑n from by field_simp,
        div_lt_iff₀ hn_pos]; linarith
  rw [h_set_eq]
  rw [show (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) : ℝ)
      = -(2 * (↑n * t) ^ 2 / ∑ i, (b i - a i) ^ 2) from by ring]
  have hY_indep : iIndepFun (β := fun _ : Fin n => ℝ) Y μ := by
    rw [hY_def]
    exact hX_indep.comp (fun i => fun x => x - ∫ ω', X i ω' ∂μ)
      (fun i => measurable_sub_const _)
  have hYm : ∀ i, Measurable (Y i) := fun i => (hXm i).sub measurable_const
  have hYi : ∀ i, Integrable (Y i) μ := fun i => (hXi i).sub (integrable_const _)
  have hYa : ∀ i, ∀ᵐ ω ∂μ, (a i - ∫ ω', X i ω' ∂μ) ≤ Y i ω := by
    intro i; filter_upwards [hXa i] with ω hω; simp [hY_def]; linarith
  have hYb : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≤ (b i - ∫ ω', X i ω' ∂μ) := by
    intro i; filter_upwards [hXb i] with ω hω; simp [hY_def]; linarith
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i; simp [hY_def]
    rw [integral_sub (hXi i) (integrable_const _)]; simp [integral_const]
  have hab' : ∀ i, (a i - ∫ ω', X i ω' ∂μ) < (b i - ∫ ω', X i ω' ∂μ) :=
    fun i => sub_lt_sub_right (hab i) _
  have h_range_eq : (∑ i, ((b i - ∫ ω', X i ω' ∂μ) - (a i - ∫ ω', X i ω' ∂μ)) ^ 2)
      = ∑ i, (b i - a i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; ring_nf
  rw [← h_range_eq]
  exact hoeffding_sum_lower_tail hab' hYm hYi hYa hYb hYmean hY_indep
    (↑n * t) (mul_pos hn_pos ht)

/-- **Theorem 1.9 (Hoeffding's inequality for the sample mean).** Combined
two-sided tail bound: for independent `X_i ∈ [a_i, b_i]`,
`max(P(X̄ - E X̄ > t), P(X̄ - E X̄ < -t)) ≤ exp(-2 n² t² / ∑ (b_i - a_i)²)`. -/
theorem theorem_1_9_sample_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ)
    (hXa : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω)
    (hXb : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b i)
    (hX_indep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n > t} ≤
      ENNReal.ofReal (exp (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) ∧
    μ {ω | (∑ i, X i ω) / ↑n - (∑ i, ∫ ω', X i ω' ∂μ) / ↑n < -t} ≤
      ENNReal.ofReal (exp (-(2 * ↑n ^ 2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))) :=
  ⟨hoeffding_sample_mean_upper_tail hn hab hXm hXi hXa hXb hX_indep t ht,
   hoeffding_sample_mean_lower_tail hn hab hXm hXi hXa hXb hX_indep t ht⟩
