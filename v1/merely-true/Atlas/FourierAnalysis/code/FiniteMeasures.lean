/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory BoundedContinuousFunction Complex MeasureTheory.Measure
open Filter Topology Metric
open scoped FourierTransform

namespace FourierTransformMeasure

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

def fourierTransformMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) : ℂ :=
  charFun μ (-ξ)

theorem continuous_fourierTransformMeasure :
    Continuous (fourierTransformMeasure μ) :=
  continuous_charFun.comp continuous_neg

theorem norm_fourierTransformMeasure_le (ξ : ℝ) :
    ‖fourierTransformMeasure μ ξ‖ ≤ μ.real Set.univ :=
  norm_charFun_le (-ξ)

def fourierTransformBCF (μ : Measure ℝ) [IsFiniteMeasure μ] : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fourierTransformMeasure μ) continuous_fourierTransformMeasure
    (μ.real Set.univ) norm_fourierTransformMeasure_le

@[simp]
theorem fourierTransformBCF_apply (ξ : ℝ) :
    fourierTransformBCF μ ξ = fourierTransformMeasure μ ξ := by
  simp [fourierTransformBCF, BoundedContinuousFunction.coe_ofNormedAddCommGroup]

theorem eq_of_fourierTransformMeasure_eq
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : fourierTransformMeasure μ = fourierTransformMeasure ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  have ht := congr_fun h (-t)
  simp only [fourierTransformMeasure, neg_neg] at ht
  exact ht

def schwartzFourierTransform (φ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun y => ∫ ξ, φ ξ * Complex.exp (-(↑y * ↑ξ * Complex.I))

theorem parseval_fubini_measure
    (μ : Measure ℝ) (hμ : IsFiniteMeasure μ) (φ : SchwartzMap ℝ ℂ) :
    ∫ ξ, φ ξ * @fourierTransformMeasure μ hμ ξ = ∫ y, schwartzFourierTransform φ y ∂μ := by

  simp only [fourierTransformMeasure, charFun_apply_real]


  have h_pull : ∀ ξ : ℝ, φ ξ * ∫ x, exp (↑(-ξ) * ↑x * Complex.I) ∂μ =
      ∫ x, φ ξ * exp (↑(-ξ) * ↑x * Complex.I) ∂μ :=
    fun ξ => (integral_const_mul _ _).symm
  simp_rw [h_pull]

  have h_integrable : Integrable
      (fun p : ℝ × ℝ => φ p.1 * exp (↑(-p.1) * ↑p.2 * Complex.I))
      (Measure.prod volume μ) := by
    apply Integrable.mono (φ.integrable.comp_fst μ)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · exact φ.continuous.comp continuous_fst
      · apply Complex.continuous_exp.comp
        apply Continuous.mul
        · apply Continuous.mul
          · exact Complex.continuous_ofReal.comp (continuous_fst.neg)
          · exact Complex.continuous_ofReal.comp continuous_snd
        · exact continuous_const
    · apply ae_of_all
      intro ⟨ξ, x⟩
      simp only
      rw [norm_mul]
      have : ‖exp (↑(-ξ) * ↑x * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [this, mul_one]
  rw [integral_integral_swap h_integrable]
  congr 1; ext y
  simp only [schwartzFourierTransform]
  congr 1; ext ξ
  congr 1; congr 1
  push_cast; ring

def mulEquiv (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.equivOfInverse
    (c • ContinuousLinearMap.id ℝ ℝ) (c⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (fun x => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hc, one_mul])
    (fun x => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hc, one_mul])

@[simp]
lemma mulEquiv_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    mulEquiv c hc x = c * x := by
  simp [mulEquiv, ContinuousLinearEquiv.equivOfInverse]

private lemma real_inner_eq_mul (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
  simp [inner, mul_comm]

lemma sft_eq_fourier_at (φ : SchwartzMap ℝ ℂ) (y : ℝ) :
    schwartzFourierTransform φ y = (𝓕 (φ : ℝ → ℂ)) (y / (2 * Real.pi)) := by
  simp only [schwartzFourierTransform, Real.fourier_eq']
  congr 1; ext ξ; rw [smul_eq_mul, mul_comm]; congr 1; congr 1
  simp only [real_inner_eq_mul]; push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem fourier_surjective_schwartz
    (f : SchwartzMap ℝ ℂ) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ y, schwartzFourierTransform φ y = f y := by

  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  let scale := mulEquiv (2 * Real.pi) h2pi
  let g : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale f

  let φ : SchwartzMap ℝ ℂ := 𝓕⁻ g
  refine ⟨φ, fun y => ?_⟩

  rw [sft_eq_fourier_at, ← SchwartzMap.fourier_coe]

  have h_inv : 𝓕 φ = g := FourierInvPair.fourier_fourierInv_eq g
  change (𝓕 φ : SchwartzMap ℝ ℂ) (y / (2 * Real.pi)) = f y
  rw [h_inv]

  show g (y / (2 * Real.pi)) = f y
  simp only [g, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  congr 1
  rw [mulEquiv_apply]
  field_simp

lemma exists_norm_le_of_tendsto {f : ℕ → ℂ} {L : ℂ}
    (hf : Tendsto f atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖f j‖ ≤ C := by
  have hbdd := Metric.isBounded_range_of_tendsto f hf
  rw [isBounded_range_iff] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C + ‖f 0‖, add_nonneg (le_trans dist_nonneg (hC 0 0)) (norm_nonneg _), fun j => ?_⟩
  calc ‖f j‖ = dist (f j) 0 := (dist_zero_right _).symm
    _ ≤ dist (f j) (f 0) + dist (f 0) 0 := dist_triangle _ _ _
    _ = dist (f j) (f 0) + ‖f 0‖ := by rw [dist_zero_right]
    _ ≤ C + ‖f 0‖ := by linarith [hC j 0]

lemma measureReal_eq_norm_charFun_zero (μ : Measure ℝ) [IsFiniteMeasure μ] :
    μ.real Set.univ = ‖charFun μ (0 : ℝ)‖ := by
  rw [charFun_zero]
  simp [Complex.norm_real, abs_of_nonneg measureReal_nonneg]

theorem schwartz_weak_convergence_of_fourierTransform_tendsto
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hconv : ∀ ξ : ℝ, Tendsto (fun j => fourierTransformMeasure (μseq j) ξ) atTop
      (𝓝 (fourierTransformMeasure ν ξ)))
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun j => ∫ x, f x ∂(μseq j)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨φ, hφ⟩ := fourier_surjective_schwartz f
  have h_eq_j : ∀ j, ∫ x, f x ∂(μseq j) =
      ∫ ξ, φ ξ * fourierTransformMeasure (μseq j) ξ := by
    intro j
    rw [parseval_fubini_measure (μseq j) inferInstance φ]
    congr 1; ext y; exact (hφ y).symm
  have h_eq_ν : ∫ x, f x ∂ν = ∫ ξ, φ ξ * fourierTransformMeasure ν ξ := by
    rw [parseval_fubini_measure ν inferInstance φ]
    congr 1; ext y; exact (hφ y).symm
  simp_rw [h_eq_j, h_eq_ν]
  have h0 := hconv 0
  simp only [fourierTransformMeasure, neg_zero] at h0
  obtain ⟨C, hC_pos, hC_bound⟩ := exists_norm_le_of_tendsto h0
  have h_ftm_bound : ∀ j ξ, ‖fourierTransformMeasure (μseq j) ξ‖ ≤ C := by
    intro j ξ
    calc ‖fourierTransformMeasure (μseq j) ξ‖
        = ‖charFun (μseq j) (-ξ)‖ := rfl
      _ ≤ (μseq j).real Set.univ := norm_charFun_le (-ξ)
      _ = ‖charFun (μseq j) (0 : ℝ)‖ := measureReal_eq_norm_charFun_zero (μseq j)
      _ ≤ C := hC_bound j
  apply tendsto_integral_of_dominated_convergence (fun ξ => C * ‖φ ξ‖)
  · intro j
    exact (φ.continuous.mul (continuous_charFun.comp continuous_neg)).aestronglyMeasurable
  · exact (φ.integrable.norm).const_mul C
  · intro j
    apply ae_of_all
    intro ξ
    calc ‖φ ξ * fourierTransformMeasure (μseq j) ξ‖
        = ‖φ ξ‖ * ‖fourierTransformMeasure (μseq j) ξ‖ := norm_mul _ _
      _ ≤ ‖φ ξ‖ * C := mul_le_mul_of_nonneg_left (h_ftm_bound j ξ) (norm_nonneg _)
      _ = C * ‖φ ξ‖ := mul_comm _ _
  · apply ae_of_all
    intro ξ
    exact (hconv ξ).const_mul (φ ξ)

end FourierTransformMeasure

namespace WeakConvergencePortmanteau

open Set ENNReal

def WeakConvergenceSmooth (μseq : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n f) → HasCompactSupport f →
    Tendsto (fun j => ∫ x, f x ∂(μseq j)) atTop (𝓝 (∫ x, f x ∂μ))

lemma exists_smooth_bump_upper (a b : ℝ) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n f) ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ x ∈ Icc a b, f x = 1) ∧
      (∀ x, f x ≠ 0 → x ∈ Ioo (a - ε) (b + ε)) := by
  have hrIn_pos : (0 : ℝ) < (b - a) / 2 := half_pos (sub_pos.mpr hab)
  have hrIn_lt_rOut : (b - a) / 2 < (b - a) / 2 + ε := by linarith
  let bump : ContDiffBump ((a + b) / 2 : ℝ) :=
    ⟨(b - a) / 2, (b - a) / 2 + ε, hrIn_pos, hrIn_lt_rOut⟩
  refine ⟨bump, fun n => bump.contDiff, bump.hasCompactSupport,
    fun x => bump.nonneg, fun x => bump.le_one, ?_, ?_⟩
  · intro x hx
    apply bump.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    constructor <;> simp only [bump] <;> linarith [hx.1, hx.2]
  · intro x hx
    have hsup : x ∈ Function.support (bump : ℝ → ℝ) := Function.mem_support.mpr hx
    rw [bump.support_eq, Real.ball_eq_Ioo] at hsup
    constructor <;> simp only [bump] at hsup <;> linarith [hsup.1, hsup.2]

lemma exists_smooth_bump_lower (a b : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε < (b - a) / 2) :
    ∃ f : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n f) ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ x ∈ Icc (a + ε) (b - ε), f x = 1) ∧
      (∀ x, f x ≠ 0 → x ∈ Ioo a b) := by
  have hrIn_pos : (0 : ℝ) < (b - a) / 2 - ε := by linarith
  have hrIn_lt_rOut : (b - a) / 2 - ε < (b - a) / 2 := by linarith
  let bump : ContDiffBump ((a + b) / 2 : ℝ) :=
    ⟨(b - a) / 2 - ε, (b - a) / 2, hrIn_pos, hrIn_lt_rOut⟩
  refine ⟨bump, fun n => bump.contDiff, bump.hasCompactSupport,
    fun x => bump.nonneg, fun x => bump.le_one, ?_, ?_⟩
  · intro x hx
    apply bump.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    constructor <;> simp only [bump] <;> linarith [hx.1, hx.2]
  · intro x hx
    have hsup : x ∈ Function.support (bump : ℝ → ℝ) := Function.mem_support.mpr hx
    rw [bump.support_eq, Real.ball_eq_Ioo] at hsup
    constructor <;> simp only [bump] at hsup <;> linarith [hsup.1, hsup.2]

lemma measure_le_ofReal_integral {μ : Measure ℝ} [IsFiniteMeasure μ]
    {S : Set ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hf_nn : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x ∈ S, (1 : ℝ) ≤ f x)
    (hf_int : Integrable f μ) :
    μ S ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  have h_real : μ.real S ≤ ∫ x, f x ∂μ := by
    rw [show μ.real S = ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ from by
      rw [integral_indicator_const _ hS]; simp]
    apply integral_mono
    · exact integrable_indicator_iff hS |>.mpr (integrable_const _)
    · exact hf_int
    · intro x; simp only [Set.indicator]; split_ifs with hx
      · exact hf_one x hx
      · exact hf_nn x
  calc μ S = ENNReal.ofReal (μ.real S) := by
        simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ S)]
    _ ≤ ENNReal.ofReal (∫ x, f x ∂μ) := ENNReal.ofReal_le_ofReal h_real

lemma ofReal_integral_le_measure {μ : Measure ℝ} [IsFiniteMeasure μ]
    {T : Set ℝ} (hT : MeasurableSet T)
    {f : ℝ → ℝ} (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ 1)
    (hf_supp : ∀ x, f x ≠ 0 → x ∈ T)
    (hf_int : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ T := by
  have h_real : ∫ x, f x ∂μ ≤ μ.real T := by
    rw [show μ.real T = ∫ x, T.indicator (fun _ => (1 : ℝ)) x ∂μ from by
      rw [integral_indicator_const _ hT]; simp]
    apply integral_mono hf_int
    · exact integrable_indicator_iff hT |>.mpr (integrable_const _)
    · intro x; simp only [Set.indicator]; split_ifs with hx
      · exact hf_le x
      · exact le_antisymm (le_of_not_gt fun hpos =>
          hx (hf_supp x (ne_of_gt hpos))) (hf_nn x) |>.le
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (μ.real T) :=
        ENNReal.ofReal_le_ofReal h_real
    _ = μ T := by simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ T)]

lemma limsup_measure_Ioo_le_of_weakConvergence
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : WeakConvergenceSmooth μseq μ)
    {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    atTop.limsup (fun j => (μseq j) (Ioo a b)) ≤ μ (Ioo (a - ε) (b + ε)) := by
  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_nn, hφ_le, hφ_one, hφ_support⟩ :=
    exists_smooth_bump_upper a b hab ε hε
  have hφ_cont : Continuous φ := (hφ_smooth 0).continuous
  have hφ_int : ∀ ν : Measure ℝ, [IsFiniteMeasure ν] → Integrable φ ν :=
    fun ν _ => hφ_cont.integrable_of_hasCompactSupport hφ_supp

  have h_tendsto_ennreal : Tendsto (fun j => ENNReal.ofReal (∫ x, φ x ∂(μseq j)))
      atTop (𝓝 (ENNReal.ofReal (∫ x, φ x ∂μ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hweak φ hφ_smooth hφ_supp)
  calc atTop.limsup (fun j => (μseq j) (Ioo a b))
      ≤ atTop.limsup (fun j => ENNReal.ofReal (∫ x, φ x ∂(μseq j))) := by
        apply limsup_le_limsup (.of_forall fun j => ?_)
        exact measure_le_ofReal_integral measurableSet_Ioo hφ_nn
          (fun x hx => by rw [hφ_one x (Ioo_subset_Icc_self hx)]) (hφ_int (μseq j))
    _ = ENNReal.ofReal (∫ x, φ x ∂μ) := h_tendsto_ennreal.limsup_eq
    _ ≤ μ (Ioo (a - ε) (b + ε)) :=
        ofReal_integral_le_measure measurableSet_Ioo hφ_nn hφ_le hφ_support (hφ_int μ)

lemma measure_Ioo_le_liminf_of_weakConvergence
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : WeakConvergenceSmooth μseq μ)
    {a b : ℝ} {ε : ℝ} (hε : 0 < ε) (hε_small : ε < (b - a) / 2) :
    μ (Ioo (a + ε) (b - ε)) ≤ atTop.liminf (fun j => (μseq j) (Ioo a b)) := by
  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_nn, hφ_le, hφ_one, hφ_support⟩ :=
    exists_smooth_bump_lower a b ε hε hε_small
  have hφ_cont : Continuous φ := (hφ_smooth 0).continuous
  have hφ_int : ∀ ν : Measure ℝ, [IsFiniteMeasure ν] → Integrable φ ν :=
    fun ν _ => hφ_cont.integrable_of_hasCompactSupport hφ_supp
  have h_tendsto_ennreal : Tendsto (fun j => ENNReal.ofReal (∫ x, φ x ∂(μseq j)))
      atTop (𝓝 (ENNReal.ofReal (∫ x, φ x ∂μ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hweak φ hφ_smooth hφ_supp)
  calc μ (Ioo (a + ε) (b - ε))
      ≤ ENNReal.ofReal (∫ x, φ x ∂μ) :=
        measure_le_ofReal_integral measurableSet_Ioo hφ_nn
          (fun x hx => by rw [hφ_one x (Ioo_subset_Icc_self hx)]) (hφ_int μ)
    _ = atTop.liminf (fun j => ENNReal.ofReal (∫ x, φ x ∂(μseq j))) :=
        h_tendsto_ennreal.liminf_eq.symm
    _ ≤ atTop.liminf (fun j => (μseq j) (Ioo a b)) := by
        apply liminf_le_liminf (.of_forall fun j => ?_)
        exact ofReal_integral_le_measure measurableSet_Ioo hφ_nn hφ_le hφ_support (hφ_int (μseq j))

theorem limsup_measure_Ioo_le_measure_Icc
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : WeakConvergenceSmooth μseq μ)
    {a b : ℝ} (hab : a < b) :
    atTop.limsup (fun j => (μseq j) (Ioo a b)) ≤ μ (Icc a b) := by


  have h_bound : ∀ n : ℕ, atTop.limsup (fun j => (μseq j) (Ioo a b)) ≤
      μ (Ioo (a - 1 / (↑n + 1)) (b + 1 / (↑n + 1))) :=
    fun n => limsup_measure_Ioo_le_of_weakConvergence μseq μ hweak hab (by positivity)

  have h_inter : (⋂ n : ℕ, Ioo (a - 1 / (↑n + 1)) (b + 1 / (↑n + 1))) = Icc a b := by
    ext x; simp only [mem_iInter, mem_Ioo, mem_Icc]
    constructor
    · intro h
      constructor
      · by_contra hlt
        have hax : 0 < a - x := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (a - x))
        have h1 : 1 / (↑n + 1) < a - x := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑n + 1)]
          have : 1 / (a - x) < ↑n + 1 := lt_trans hn (by linarith)
          rw [div_lt_iff₀ hax] at this
          linarith [mul_comm (a - x) (↑n + 1)]
        linarith [(h n).1]
      · by_contra hlt
        have hxb : 0 < x - b := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (x - b))
        have h1 : 1 / (↑n + 1) < x - b := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑n + 1)]
          have : 1 / (x - b) < ↑n + 1 := lt_trans hn (by linarith)
          rw [div_lt_iff₀ hxb] at this
          linarith [mul_comm (x - b) (↑n + 1)]
        linarith [(h n).2]
    · intro ⟨hxa, hxb⟩ n
      exact ⟨by linarith [show (0 : ℝ) < 1 / (↑n + 1) from by positivity],
             by linarith [show (0 : ℝ) < 1 / (↑n + 1) from by positivity]⟩

  have h_anti : Antitone (fun n : ℕ => Ioo (a - 1 / (↑n + 1)) (b + 1 / (↑n + 1))) := by
    intro m n hmn
    apply Ioo_subset_Ioo <;> gcongr
  have h_meas : ∀ n : ℕ, NullMeasurableSet (Ioo (a - 1 / (↑n + 1)) (b + 1 / (↑n + 1))) μ :=
    fun n => measurableSet_Ioo.nullMeasurableSet
  have h_fin : ∃ n : ℕ, μ (Ioo (a - 1 / (↑n + 1)) (b + 1 / (↑n + 1))) ≠ ⊤ :=
    ⟨0, measure_ne_top μ _⟩
  have h_tendsto := tendsto_measure_iInter_atTop h_meas h_anti h_fin
  simp only [h_inter] at h_tendsto
  exact ge_of_tendsto h_tendsto (.of_forall h_bound)

theorem measure_Ioo_le_liminf_measure_Ioo
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : WeakConvergenceSmooth μseq μ)
    {a b : ℝ} (_hab : a < b) :
    μ (Ioo a b) ≤ atTop.liminf (fun j => (μseq j) (Ioo a b)) := by

  let S : ℕ → Set ℝ := fun n => Ioo (a + 1 / (↑n + 1)) (b - 1 / (↑n + 1))
  have hS_mono : Monotone S := by
    intro m n hmn
    apply Ioo_subset_Ioo <;> gcongr
  have h_union : Ioo a b = ⋃ n, S n := by
    ext x; simp only [S, mem_Ioo, mem_iUnion]
    constructor
    · intro ⟨hxa, hxb⟩
      have hδ : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hxa) (sub_pos.mpr hxb)
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / min (x - a) (b - x))
      have key : 1 / (↑n + 1) < min (x - a) (b - x) := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑n + 1)]
        have : 1 / min (x - a) (b - x) < ↑n + 1 := lt_trans hn (by linarith)
        rw [div_lt_iff₀ hδ] at this
        linarith [mul_comm (min (x - a) (b - x)) (↑n + 1)]
      exact ⟨n, by linarith [min_le_left (x - a) (b - x)],
               by linarith [min_le_right (x - a) (b - x)]⟩
    · intro ⟨n, hxa, hxb⟩
      exact ⟨by linarith [show (0 : ℝ) < 1 / (↑n + 1) from by positivity],
             by linarith [show (0 : ℝ) < 1 / (↑n + 1) from by positivity]⟩

  have h_sup : μ (Ioo a b) = ⨆ n, μ (S n) := by
    rw [h_union]; exact hS_mono.measure_iUnion
  rw [h_sup]
  apply iSup_le
  intro n
  by_cases hε_small : 1 / ((n : ℝ) + 1) < (b - a) / 2
  · exact measure_Ioo_le_liminf_of_weakConvergence μseq μ hweak (by positivity) hε_small
  · simp only [not_lt] at hε_small
    have : S n = ∅ := Ioo_eq_empty (by linarith)
    simp [this]

theorem tendsto_measure_Ioo_of_no_atoms
    (μseq : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (μseq j)]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hweak : WeakConvergenceSmooth μseq μ)
    {a b : ℝ} (hab : a < b)
    (ha : μ {a} = 0) (hb : μ {b} = 0) :
    Tendsto (fun j => (μseq j) (Ioo a b)) atTop (𝓝 (μ (Ioo a b))) := by

  have h_Icc_eq : μ (Icc a b) = μ (Ioo a b) := by
    apply le_antisymm
    · calc μ (Icc a b) ≤ μ (Ioo a b ∪ {a} ∪ {b}) := by
            apply measure_mono
            intro x ⟨hxa, hxb⟩
            rcases eq_or_lt_of_le hxa with rfl | hxa'
            · exact Or.inl (Or.inr rfl)
            · rcases eq_or_lt_of_le hxb with rfl | hxb'
              · exact Or.inr rfl
              · exact Or.inl (Or.inl ⟨hxa', hxb'⟩)
        _ ≤ μ (Ioo a b ∪ {a}) + μ {b} := measure_union_le _ _
        _ ≤ (μ (Ioo a b) + μ {a}) + μ {b} := by gcongr; exact measure_union_le _ _
        _ = μ (Ioo a b) := by rw [ha, hb, add_zero, add_zero]
    · exact measure_mono Ioo_subset_Icc_self


  exact tendsto_of_le_liminf_of_limsup_le
    (measure_Ioo_le_liminf_measure_Ioo μseq μ hweak hab)
    (h_Icc_eq ▸ limsup_measure_Ioo_le_measure_Icc μseq μ hweak hab)

end WeakConvergencePortmanteau

end
