/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Atlas.ComplexVariables.code.Lecture13

open Complex InnerProductSpace Laplacian Metric Real Set Topology Filter MeasureTheory

abbrev IsHarmonic (u : ℂ → ℝ) (Ω : Set ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u Ω

lemma IsHarmonic.contDiffOn {u : ℂ → ℝ} {Ω : Set ℂ} (hu : IsHarmonic u Ω) :
    ContDiffOn ℝ 2 u Ω :=
  HarmonicOnNhd.contDiffOn hu

lemma IsHarmonic.harmonicAt {u : ℂ → ℝ} {Ω : Set ℂ} (hu : IsHarmonic u Ω)
    {z : ℂ} (hz : z ∈ Ω) : HarmonicAt u z :=
  hu z hz

lemma IsHarmonic.mono {u : ℂ → ℝ} {Ω₁ Ω₂ : Set ℂ} (hu : IsHarmonic u Ω₁) (h : Ω₂ ⊆ Ω₁) :
    IsHarmonic u Ω₂ :=
  HarmonicOnNhd.mono hu h

noncomputable section PoissonIntegralSetup

def poissonIntegral (U : ℂ → ℝ) (a : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 a • U) 0 1

def herglotzIntegral (U : ℂ → ℝ) (a : ℂ) : ℂ :=
  (2 * (π : ℝ))⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    herglotzRieszKernel 0 a (circleMap 0 1 θ) • (U (circleMap 0 1 θ) : ℂ)

theorem poissonIntegral_eq_re_herglotzIntegral
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    poissonIntegral U a = (herglotzIntegral U a).re := by
  simp only [poissonIntegral, herglotzIntegral, Real.circleAverage]
  rw [Complex.smul_re]
  congr 1

  have hInt : IntervalIntegrable
    (fun θ => herglotzRieszKernel 0 a (circleMap 0 1 θ) • (U (circleMap 0 1 θ) : ℂ))
    volume 0 (2 * π) := by
    apply IntervalIntegrable.continuousOn_smul
    · exact ⟨hU.1.ofReal, hU.2.ofReal⟩
    · simp only [herglotzRieszKernel_fun_def, sub_zero]
      apply ContinuousOn.div
      · exact ((continuous_circleMap 0 1).add continuous_const).continuousOn
      · exact ((continuous_circleMap 0 1).sub continuous_const).continuousOn
      · intro θ _
        simp only [sub_ne_zero]
        intro h
        rw [Metric.mem_ball, dist_zero_right] at ha
        have hmem := circleMap_mem_sphere 0 one_pos.le θ
        rw [Metric.mem_sphere, dist_zero_right] at hmem
        linarith [hmem ▸ h ▸ ha]

  rw [show (∫ θ in (0 : ℝ)..2 * π, herglotzRieszKernel 0 a (circleMap 0 1 θ) •
    (U (circleMap 0 1 θ) : ℂ)).re =
    reCLM (∫ θ in (0 : ℝ)..2 * π, herglotzRieszKernel 0 a (circleMap 0 1 θ) •
    (U (circleMap 0 1 θ) : ℂ)) from by simp [reCLM_apply]]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm reCLM hInt]
  congr 1
  ext θ
  simp only [reCLM_apply]

  change poissonKernel 0 a (circleMap 0 1 θ) * U (circleMap 0 1 θ) = _
  change _ = (herglotzRieszKernel 0 a (circleMap 0 1 θ) * ↑(U (circleMap 0 1 θ))).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h := congr_fun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := a)) (circleMap 0 1 θ)
  simp only [Function.comp_apply] at h
  rw [h]

set_option maxHeartbeats 1600000 in
theorem herglotzIntegral_differentiableOn
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1) :
    DifferentiableOn ℂ (herglotzIntegral U) (ball 0 1) := by
  intro a₀ ha₀
  rw [mem_ball_zero_iff] at ha₀
  have r₀_lt : max ‖a₀‖ (1/2 : ℝ) < 1 := max_lt ha₀ (by norm_num)
  have ε₀_val : (1 - max ‖a₀‖ (1/2 : ℝ)) / 2 > 0 := by linarith
  have hU_int : IntervalIntegrable (fun θ => U (circleMap 0 1 θ)) volume 0 (2 * π) :=
    (circleIntegrable_def U 0 1).mp hU

  have huIoc : Set.uIoc (0 : ℝ) (2 * π) = Set.Ioc 0 (2 * π) :=
    Set.uIoc_of_le (by linarith [Real.pi_pos])
  have hU_meas : AEStronglyMeasurable (fun θ => (U (circleMap 0 1 θ) : ℂ))
      (volume.restrict (Set.uIoc 0 (2 * π))) := by
    rw [huIoc]
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable hU_int.aestronglyMeasurable

  suffices DifferentiableAt ℂ (herglotzIntegral U) a₀ from this.differentiableWithinAt
  unfold herglotzIntegral
  simp_rw [herglotzRieszKernel_def, sub_zero, smul_eq_mul, Complex.real_smul]
  apply DifferentiableAt.const_mul

  set ε₀ := (1 - max ‖a₀‖ (1/2 : ℝ)) / 2

  have hx_norm : ∀ x ∈ ball a₀ ε₀, ‖x‖ < 1 - ε₀ := by
    intro x hx
    rw [mem_ball, Complex.dist_eq] at hx
    have h1 : ‖x‖ ≤ ‖a₀‖ + ‖x - a₀‖ := norm_le_insert' x a₀
    have h2 : ‖a₀‖ ≤ max ‖a₀‖ (1/2 : ℝ) := le_max_left _ _
    have h3 : max ‖a₀‖ (1/2 : ℝ) + ε₀ = 1 - ε₀ := by simp [ε₀]; ring
    linarith

  have hzx_bound : ∀ x ∈ ball a₀ ε₀, ∀ θ : ℝ,
      ‖circleMap 0 1 θ - x‖ ≥ ε₀ := by
    intro x hx θ
    have hxn := hx_norm x hx
    have : ‖circleMap 0 1 θ‖ = 1 := by rw [norm_circleMap_zero]; simp
    have : ε₀ < 1 - ‖x‖ := by linarith
    linarith [norm_sub_norm_le (circleMap 0 1 θ) x]

  have hzx_ne : ∀ x ∈ ball a₀ ε₀, ∀ θ : ℝ,
      circleMap 0 1 θ - x ≠ 0 := by
    intro x hx θ h
    have := hzx_bound x hx θ
    simp [h] at this; linarith

  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 2 * π) (x₀ := a₀)
    (F := fun y θ => (circleMap 0 1 θ + y) / (circleMap 0 1 θ - y) * ↑(U (circleMap 0 1 θ)))
    (F' := fun y θ => 2 * circleMap 0 1 θ / (circleMap 0 1 θ - y) ^ 2 * ↑(U (circleMap 0 1 θ)))
    (bound := fun θ => 2 / ε₀ ^ 2 * ‖(U (circleMap 0 1 θ) : ℂ)‖)
    (s := ball a₀ ε₀)
    ?hs ?hF_meas ?hF_int ?hF'_meas ?h_bound ?bound_int ?h_diff).2.differentiableAt
  · exact key
  case hs => exact ball_mem_nhds a₀ ε₀_val
  case hF_meas =>
    apply eventually_of_mem (ball_mem_nhds a₀ ε₀_val)
    intro x hx
    have hcont : Continuous (fun θ => (circleMap 0 1 θ + x) / (circleMap 0 1 θ - x)) := by
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro θ; exact hzx_ne x hx θ
    exact hcont.aestronglyMeasurable.mul hU_meas
  case hF_int =>
    have hcont : ContinuousOn (fun θ => (circleMap 0 1 θ + a₀) / (circleMap 0 1 θ - a₀))
        (Set.uIcc 0 (2 * π)) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro θ _; exact hzx_ne a₀ (mem_ball_self ε₀_val) θ
    exact IntervalIntegrable.continuousOn_mul ⟨hU_int.1.ofReal, hU_int.2.ofReal⟩ hcont
  case hF'_meas =>
    have hcont : Continuous (fun θ => 2 * circleMap 0 1 θ / (circleMap 0 1 θ - a₀) ^ 2) := by
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro θ; exact pow_ne_zero 2 (hzx_ne a₀ (mem_ball_self ε₀_val) θ)
    exact hcont.aestronglyMeasurable.mul hU_meas
  case h_bound =>
    filter_upwards with θ hθ x hx
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hzx := hzx_bound x hx θ
    have hεp : (0 : ℝ) < ε₀ := ε₀_val
    have hz : ‖circleMap 0 1 θ‖ = 1 := by rw [norm_circleMap_zero]; simp
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, hz, mul_one]
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by positivity)
    exact pow_le_pow_left₀ (by linarith) hzx 2
  case bound_int =>
    apply IntervalIntegrable.const_mul
    simp_rw [Complex.norm_real]
    exact ⟨hU_int.1.norm, hU_int.2.norm⟩

  case h_diff =>
    filter_upwards with θ hθ x hx
    have hne := hzx_ne x hx θ
    have h1 : HasDerivAt (fun a => circleMap 0 1 θ + a) 1 x :=
      (hasDerivAt_id x).const_add _
    have h2 : HasDerivAt (fun a => circleMap 0 1 θ - a) (-1) x := by
      have := (hasDerivAt_const x (circleMap 0 1 θ)).sub (hasDerivAt_id x)
      simp at this; exact this
    have hdiv := h1.div h2 hne
    have hderiv : HasDerivAt (fun a => (circleMap 0 1 θ + a) / (circleMap 0 1 θ - a))
        (2 * circleMap 0 1 θ / (circleMap 0 1 θ - x) ^ 2) x := by
      refine hdiv.congr_deriv ?_; field_simp; ring
    exact hderiv.mul_const _

theorem harmonicOnNhd_re_of_differentiableOn
    {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    HarmonicOnNhd (fun z ↦ (f z).re) s := by
  intro z hz
  exact AnalyticAt.harmonicAt_re ((hf.analyticOnNhd hs) z hz)

noncomputable def mobiusTransform (a z : ℂ) : ℂ :=
  (z + a) / (starRingEnd ℂ a * z + 1)

lemma continuous_poissonKernel_circleMap (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    Continuous (fun t => poissonKernel 0 a (circleMap 0 1 t)) := by
  unfold poissonKernel; simp only [sub_zero]
  apply Continuous.div
  · exact (continuous_norm.pow 2 |>.comp (continuous_circleMap 0 1)).sub continuous_const
  · exact continuous_norm.pow 2 |>.comp ((continuous_circleMap 0 1).sub continuous_const)
  · intro t; simp only [ne_eq]
    rw [pow_eq_zero_iff (by norm_num : 2 ≠ 0), norm_eq_zero, sub_eq_zero]
    intro heq
    have h1 : ‖circleMap 0 1 t‖ = 1 := by
      have := circleMap_mem_sphere 0 one_pos.le t
      rw [Metric.mem_sphere, dist_zero_right] at this; exact this
    have h2 : ‖a‖ < 1 := by rw [mem_ball, dist_zero_right] at ha; exact ha
    rw [heq] at h1; linarith

noncomputable def invMobiusAngle (a : ℂ) (_ha : a ∈ ball (0 : ℂ) 1) : ℝ → ℝ :=
  fun θ => Complex.arg ((1 - a) / (1 - starRingEnd ℂ a)) +
    ∫ t in (0 : ℝ)..θ, poissonKernel 0 a (circleMap 0 1 t)

lemma mobiusTransform_circleMap_invMobiusAngle_zero (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    mobiusTransform a (circleMap 0 1 (invMobiusAngle a ha 0)) = 1 := by

  simp only [invMobiusAngle, intervalIntegral.integral_same, add_zero]


  set u := (1 - a) / (1 - starRingEnd ℂ a) with hu_def

  have hconj_sub : (1 : ℂ) - starRingEnd ℂ a = starRingEnd ℂ (1 - a) := by
    simp [map_sub]
  have ha_norm : ‖a‖ < 1 := by rwa [mem_ball, dist_zero_right] at ha
  have h1_sub_a_ne : (1 : ℂ) - a ≠ 0 := by
    intro h
    have ha1 : a = 1 := by rwa [sub_eq_zero, eq_comm] at h
    rw [ha1] at ha_norm; simp at ha_norm

  have h1_sub_conj_ne : (1 : ℂ) - starRingEnd ℂ a ≠ 0 := by
    rw [hconj_sub]
    intro h
    apply h1_sub_a_ne
    have : ‖starRingEnd ℂ (1 - a)‖ = 0 := by rw [h, norm_zero]
    rwa [Complex.norm_conj, norm_eq_zero] at this

  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def, norm_div, hconj_sub, Complex.norm_conj, div_self]
    exact norm_ne_zero_iff.mpr h1_sub_a_ne
  have hu_ne : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu_norm]; exact one_ne_zero)

  have hcircle : circleMap 0 1 (arg u) = u := by
    rw [circleMap_zero, show (1 : ℝ) = ‖u‖ from hu_norm.symm]
    exact norm_mul_exp_arg_mul_I u

  rw [hcircle]


  rw [mobiusTransform, div_eq_one_iff_eq]
  ·
    rw [hu_def]
    have : (1 : ℂ) - starRingEnd ℂ a ≠ 0 := h1_sub_conj_ne
    field_simp
    ring
  ·
    rw [hu_def]
    rw [show starRingEnd ℂ a * ((1 - a) / (1 - starRingEnd ℂ a)) + 1 =
        (starRingEnd ℂ a * (1 - a) + (1 - starRingEnd ℂ a)) / (1 - starRingEnd ℂ a) by
      field_simp]
    apply div_ne_zero
    ·

      have hkey : starRingEnd ℂ a * (1 - a) + (1 - starRingEnd ℂ a) = 1 - starRingEnd ℂ a * a := by
        ring
      rw [hkey]
      intro h
      have h1 : starRingEnd ℂ a * a = 1 := by rwa [sub_eq_zero, eq_comm] at h

      have : ‖starRingEnd ℂ a * a‖ = 1 := by rw [h1]; simp
      rw [norm_mul, Complex.norm_conj] at this

      have hmul : ‖a‖ * ‖a‖ = 1 := this
      have : ‖a‖ * ‖a‖ < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a) ha_norm ha_norm.le
      linarith
    · exact h1_sub_conj_ne

lemma eq_zero_of_hasDerivAt_mul {y : ℝ → ℂ} {c : ℝ → ℂ}
    (hc_cont : Continuous c)
    (hy_deriv : ∀ θ, HasDerivAt y (c θ * y θ) θ)
    (hy0 : y 0 = 0) (θ : ℝ) : y θ = 0 := by
  set G : ℝ → ℂ := fun θ => ∫ t in (0:ℝ)..θ, c t with hG_def
  set E : ℝ → ℂ := fun θ => Complex.exp (-G θ) with hE_def
  set u : ℝ → ℂ := fun θ => y θ * E θ with hu_def
  have hG_deriv : ∀ θ, HasDerivAt G (c θ) θ := fun θ =>
    intervalIntegral.integral_hasDerivAt_right
      (hc_cont.intervalIntegrable _ _)
      (hc_cont.stronglyMeasurableAtFilter _ _)
      hc_cont.continuousAt
  have hE_deriv : ∀ θ, HasDerivAt E (-c θ * E θ) θ := by
    intro θ
    have h1 := Complex.hasDerivAt_exp (-G θ)
    have h2 : HasDerivAt (fun t => -G t) (-c θ) θ := (hG_deriv θ).neg
    convert (h1.comp θ h2) using 1; ring
  have hu_deriv : ∀ θ, HasDerivAt u 0 θ := by
    intro θ
    convert (hy_deriv θ).mul (hE_deriv θ) using 1
    simp [hE_def]; ring
  have hu_diff : Differentiable ℝ u := fun x => (hu_deriv x).differentiableAt
  have hu_deriv_eq : ∀ x, deriv u x = 0 := fun x => (hu_deriv x).deriv
  have hu_const : u θ = u 0 := is_const_of_deriv_eq_zero hu_diff hu_deriv_eq θ 0
  have hu0 : u 0 = 0 := by simp [hu_def, hy0]
  have huθ : u θ = 0 := by rw [hu_const, hu0]
  have hE_ne : E θ ≠ 0 := by simp [hE_def]
  exact (mul_eq_zero.mp huθ).resolve_right hE_ne

lemma deriv_inv_mobius_eq_poisson_mul' (a z : ℂ) (hz : ‖z‖ = 1)
    (hd : 1 - starRingEnd ℂ a * z ≠ 0) (hza : z - a ≠ 0) :
    ((1 - starRingEnd ℂ a * a) / (1 - starRingEnd ℂ a * z) ^ 2) * (z * Complex.I) =
    ↑(poissonKernel 0 a z) * ((z - a) / (1 - starRingEnd ℂ a * z) * Complex.I) := by
  have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hz_conj : z * starRingEnd ℂ z = 1 := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hz]
  have h_nsq : (↑(‖z - a‖ ^ 2) : ℂ) * z = (z - a) * (1 - starRingEnd ℂ a * z) := by
    have : (↑(‖z - a‖ ^ 2) : ℂ) = (z - a) * starRingEnd ℂ (z - a) := by
      rw [show (↑(‖z - a‖ ^ 2) : ℂ) = ↑(Complex.normSq (z - a)) from by
        simp [Complex.normSq_eq_norm_sq]]
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [this, map_sub]
    have hcz : starRingEnd ℂ z * z = 1 := by rw [← hz_conj]; ring
    suffices (starRingEnd ℂ z - starRingEnd ℂ a) * z = 1 - starRingEnd ℂ a * z by
      rw [mul_assoc, this]
    linear_combination hcz
  have hP : poissonKernel 0 a z = (1 - ‖a‖ ^ 2) / ‖z - a‖ ^ 2 := by
    unfold poissonKernel; simp [hz]
  have h_nsq_div : (↑(‖z - a‖ ^ 2) : ℂ) = (z - a) * (1 - starRingEnd ℂ a * z) / z := by
    rw [eq_div_iff hz_ne]; exact h_nsq
  have h1a : Complex.ofReal (1 - ‖a‖ ^ 2) = 1 - starRingEnd ℂ a * a := by
    have : Complex.ofReal (‖a‖ ^ 2) = starRingEnd ℂ a * a := by
      rw [← Complex.normSq_eq_conj_mul_self]; simp [Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, this]
  rw [hP, Complex.ofReal_div, h1a, h_nsq_div]
  field_simp

lemma one_sub_conj_mul_circleMap_ne_zero (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    1 - starRingEnd ℂ a * circleMap 0 1 θ ≠ 0 := by
  intro h
  have ha_norm : ‖a‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at ha
  have hz_norm : ‖circleMap 0 1 θ‖ = 1 := by
    have := circleMap_mem_sphere 0 one_pos.le θ
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have h1 : starRingEnd ℂ a * circleMap 0 1 θ = 1 := by
    have := sub_eq_zero.mp h; exact this.symm
  have hle : ‖starRingEnd ℂ a * circleMap 0 1 θ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha_norm (le_of_eq hz_norm)
  rw [h1] at hle; simp at hle

theorem invMobiusAngle_mobiusTransform_axiom (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    mobiusTransform a (circleMap 0 1 (invMobiusAngle a ha θ)) = circleMap 0 1 θ := by


  have ha' : ‖a‖ < 1 := by rw [mem_ball, dist_zero_right] at ha; exact ha
  set c := starRingEnd ℂ a with hc_def

  let φ : ℝ → ℂ := fun t => circleMap 0 1 (invMobiusAngle a ha t)
  let w : ℝ → ℂ := fun t => (circleMap 0 1 t - a) / (1 - c * circleMap 0 1 t)
  let P : ℝ → ℝ := fun t => poissonKernel 0 a (circleMap 0 1 t)

  have hz_norm : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by
    have := circleMap_mem_sphere 0 one_pos.le t
    rw [Metric.mem_sphere, dist_zero_right] at this; exact this

  have hd : ∀ t, (1 : ℂ) - c * circleMap 0 1 t ≠ 0 :=
    fun t => one_sub_conj_mul_circleMap_ne_zero a ha t

  have hca : (1 : ℂ) - c * a ≠ 0 := by
    intro h
    have h1 : c * a = 1 := by rwa [sub_eq_zero, eq_comm] at h
    have : ‖c * a‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_conj] at this
    have : ‖a‖ * ‖a‖ = 1 := this
    have : ‖a‖ * ‖a‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a) ha' ha'.le
    linarith

  have hza : ∀ t, circleMap 0 1 t - a ≠ 0 := fun t => by
    intro h
    have heq : a = circleMap 0 1 t := by rwa [sub_eq_zero, eq_comm] at h
    rw [heq, hz_norm] at ha'; linarith


  have hφ_deriv : ∀ t, HasDerivAt φ (↑(P t) * (φ t * Complex.I)) t := fun t => by

    have hcont := continuous_poissonKernel_circleMap a ha
    have h_int : HasDerivAt (fun θ₀ => ∫ s in (0 : ℝ)..θ₀,
        poissonKernel 0 a (circleMap 0 1 s))
      (poissonKernel 0 a (circleMap 0 1 t)) t := by
      apply intervalIntegral.integral_hasDerivAt_right
      · exact hcont.intervalIntegrable _ _
      · exact hcont.stronglyMeasurableAtFilter _ _
      · exact hcont.continuousAt
    have h_const : HasDerivAt (fun _ : ℝ => Complex.arg ((1 - a) / (1 - starRingEnd ℂ a))) 0 t :=
      hasDerivAt_const t _
    have hψ : HasDerivAt (invMobiusAngle a ha) (P t) t := by
      have h3 := h_const.add h_int; simp only [zero_add] at h3; exact h3

    have hcm := hasDerivAt_circleMap 0 1 (invMobiusAngle a ha t)
    simp at hcm
    convert (hcm.scomp t hψ) using 1


  have hw_deriv : ∀ t, HasDerivAt w (↑(P t) * (w t * Complex.I)) t := fun t => by
    set z := circleMap 0 1 t with hz_def

    have hcm : HasDerivAt (circleMap 0 1) (z * Complex.I) t := by
      have := hasDerivAt_circleMap 0 1 t; simp at this; exact this

    have hT : HasDerivAt (fun z => (z - a) / (1 - c * z)) ((1 - c * a) / (1 - c * z) ^ 2) z := by
      have h1 : HasDerivAt (fun z => z - a) 1 z := by
        convert (hasDerivAt_id z).sub (hasDerivAt_const z a) using 1; ring
      have h2 : HasDerivAt (fun z => 1 - c * z) (-c) z := by
        convert (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_const z c).mul (hasDerivAt_id z))
          using 1; simp [mul_comm]
      convert h1.div h2 (hd t) using 1; field_simp; ring

    have hchain := hT.comp t hcm

    have halg := deriv_inv_mobius_eq_poisson_mul' a z (hz_norm t) (hd t) (hza t)
    convert hchain using 1
    exact halg.symm


  have hP_cont : Continuous (fun t => ↑(P t) * Complex.I) := by
    exact (continuous_ofReal.comp (continuous_poissonKernel_circleMap a ha)).mul continuous_const

  have hh_deriv : ∀ t, HasDerivAt (fun t => φ t - w t)
      ((↑(P t) * Complex.I) * (φ t - w t)) t := fun t => by
    have := (hφ_deriv t).sub (hw_deriv t)
    convert this using 1; ring

  have h0 : φ 0 - w 0 = 0 := by
    rw [sub_eq_zero]


    have hS := mobiusTransform_circleMap_invMobiusAngle_zero a ha


    rw [mobiusTransform] at hS

    have hden0 : c * φ 0 + 1 ≠ 0 := by
      intro h
      have : (φ 0 + a) / (c * φ 0 + 1) = 1 := hS
      rw [h, div_zero] at this; exact one_ne_zero this.symm
    have hnum : φ 0 + a = c * φ 0 + 1 := by
      rwa [div_eq_one_iff_eq hden0] at hS

    have hφ_eq : φ 0 * (1 - c) = 1 - a := by linear_combination hnum

    show φ 0 = w 0
    have hcm0 : circleMap 0 1 (0 : ℝ) = 1 := by simp [circleMap_zero]
    change φ 0 = (circleMap 0 1 0 - a) / (1 - c * circleMap 0 1 0)
    rw [hcm0, mul_one]

    have h1c : (1 : ℂ) - c ≠ 0 := by
      intro h
      have hc1 : c = 1 := by rwa [sub_eq_zero, eq_comm] at h
      have : ‖c‖ = 1 := by rw [hc1]; simp
      rw [RCLike.norm_conj] at this
      linarith
    rw [eq_div_iff h1c]
    exact hφ_eq


  have huniq : ∀ t, φ t - w t = 0 :=
    eq_zero_of_hasDerivAt_mul hP_cont hh_deriv h0

  have hφw : φ θ = w θ := sub_eq_zero.mp (huniq θ)

  rw [show circleMap 0 1 (invMobiusAngle a ha θ) = φ θ from rfl, hφw]


  show mobiusTransform a ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) = circleMap 0 1 θ
  rw [mobiusTransform]

  have hD_ne : c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) + 1 ≠ 0 := by
    have h1 : c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) + 1 =
        (1 - c * a) / (1 - c * circleMap 0 1 θ) := by
      rw [show c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) =
        (circleMap 0 1 θ - a) * c / (1 - c * circleMap 0 1 θ) from by ring_nf]
      rw [div_add_one (hd θ)]; congr 1; ring
    rw [h1]; exact div_ne_zero hca (hd θ)
  rw [div_eq_iff hD_ne, eq_comm]
  have key : ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ) + a) *
      (1 - c * circleMap 0 1 θ) =
      circleMap 0 1 θ * (c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) + 1) *
      (1 - c * circleMap 0 1 θ) := by
    rw [add_mul, div_mul_cancel₀ _ (hd θ), mul_assoc, add_mul]
    rw [show c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ)) *
        (1 - c * circleMap 0 1 θ) =
        c * ((circleMap 0 1 θ - a) / (1 - c * circleMap 0 1 θ) *
        (1 - c * circleMap 0 1 θ)) from by ring]
    rw [div_mul_cancel₀ _ (hd θ)]; ring
  exact mul_right_cancel₀ (hd θ) key.symm

theorem invMobiusAngle_mobiusTransform (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    mobiusTransform a (circleMap 0 1 (invMobiusAngle a ha θ)) = circleMap 0 1 θ :=
  invMobiusAngle_mobiusTransform_axiom a ha θ

theorem hasDerivAt_invMobiusAngle (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    HasDerivAt (invMobiusAngle a ha) (poissonKernel 0 a (circleMap 0 1 θ)) θ := by
  have hcont := continuous_poissonKernel_circleMap a ha
  have h1 : HasDerivAt (fun θ₀ => ∫ t in (0 : ℝ)..θ₀,
      poissonKernel 0 a (circleMap 0 1 t))
    (poissonKernel 0 a (circleMap 0 1 θ)) θ := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hcont.intervalIntegrable _ _
    · exact hcont.stronglyMeasurableAtFilter _ _
    · exact hcont.continuousAt
  have h2 : HasDerivAt (fun _ : ℝ => Complex.arg ((1 - a) / (1 - starRingEnd ℂ a))) 0 θ :=
    hasDerivAt_const θ _
  have h3 := h2.add h1
  simp only [zero_add] at h3
  exact h3

theorem invMobiusAngle_add_two_pi (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    invMobiusAngle a ha (θ + 2 * π) = invMobiusAngle a ha θ + 2 * π := by
  simp only [invMobiusAngle]
  have hcont := continuous_poissonKernel_circleMap a ha
  suffices h : ∫ t in (0 : ℝ)..(θ + 2 * π), poissonKernel 0 a (circleMap 0 1 t) =
      (∫ t in (0 : ℝ)..θ, poissonKernel 0 a (circleMap 0 1 t)) + 2 * π by linarith
  have hint : ∀ (x y : ℝ), IntervalIntegrable
      (fun t => poissonKernel 0 a (circleMap 0 1 t)) volume x y :=
    hcont.intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 θ) (hint θ (θ + 2 * π))
  have hperiod : Function.Periodic (fun t => poissonKernel 0 a (circleMap 0 1 t)) (2 * π) := by
    intro t; show poissonKernel 0 a (circleMap 0 1 (t + 2 * π)) =
      poissonKernel 0 a (circleMap 0 1 t)
    rw [periodic_circleMap 0 1 t]
  have hshift := hperiod.intervalIntegral_add_eq 0 θ
  simp only [zero_add] at hshift
  have h_int_eq : ∫ t in (0 : ℝ)..(2 * π), poissonKernel 0 a (circleMap 0 1 t) = 2 * π := by
    have h4 : Real.circleAverage (poissonKernel 0 a • fun _ => (1 : ℝ)) 0 1 = 1 := by
      apply InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      · exact fun z _ => harmonicAt_const 1
      · exact ha
    rw [Real.circleAverage_def] at h4
    have key : ∀ t, (poissonKernel 0 a • fun _ => (1 : ℝ)) (circleMap 0 1 t) =
        poissonKernel 0 a (circleMap 0 1 t) := by
      intro t; simp [smul_eq_mul]
    simp_rw [key] at h4
    rw [smul_eq_mul] at h4
    have hpi : (0 : ℝ) < 2 * π := by positivity
    nlinarith [mul_inv_cancel₀ (ne_of_gt hpi)]
  linarith

lemma norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  have h := circleMap_mem_sphere 0 one_pos.le θ
  rw [Metric.mem_sphere, dist_zero_right] at h; exact h

lemma poissonKernel_nonneg_circleMap (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) (θ : ℝ) :
    0 ≤ poissonKernel 0 a (circleMap 0 1 θ) := by
  simp only [poissonKernel_def, sub_zero]
  apply div_nonneg
  · rw [norm_circleMap_zero_one, one_pow, sub_nonneg, sq_le_one_iff_abs_le_one, abs_norm]
    rw [mem_ball, dist_zero_right] at ha; exact ha.le
  · positivity

theorem poissonIntegral_eq_circleAverage_mobiusTransform
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1) (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    poissonIntegral U a = Real.circleAverage (U ∘ mobiusTransform a) 0 1 := by
  simp only [poissonIntegral, Real.circleAverage]
  congr 1
  set ψ := invMobiusAngle a ha
  set φ' : ℝ → ℝ := fun θ => poissonKernel 0 a (circleMap 0 1 θ)
  set g : ℝ → ℝ := fun t => U (mobiusTransform a (circleMap 0 1 t))

  have h_eq : ∀ θ, (poissonKernel 0 a • U) (circleMap 0 1 θ) = φ' θ • (g ∘ ψ) θ := by
    intro θ
    simp only [smul_eq_mul, Function.comp_apply]
    show poissonKernel 0 a (circleMap 0 1 θ) * U (circleMap 0 1 θ) =
      poissonKernel 0 a (circleMap 0 1 θ) * U (mobiusTransform a (circleMap 0 1 (ψ θ)))
    rw [invMobiusAngle_mobiusTransform]
  simp_rw [h_eq]

  have hcov : ∫ θ in (0 : ℝ)..2 * π, φ' θ • (g ∘ ψ) θ =
      ∫ u in ψ 0..ψ (2 * π), g u := by
    apply intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    · exact (continuous_iff_continuousAt.mpr
        (fun x => (hasDerivAt_invMobiusAngle a ha x).continuousAt)).continuousOn
    · intro x _; exact hasDerivAt_invMobiusAngle a ha x
    · intro x _; exact poissonKernel_nonneg_circleMap a ha x
  rw [hcov]

  have hψ_shift : ψ (2 * π) = ψ 0 + 2 * π := by
    have := invMobiusAngle_add_two_pi a ha 0; simp only [zero_add] at this; exact this
  rw [hψ_shift]

  have hg_periodic : Function.Periodic g (2 * π) := by
    intro t
    show U (mobiusTransform a (circleMap 0 1 (t + 2 * π))) =
      U (mobiusTransform a (circleMap 0 1 t))
    rw [periodic_circleMap 0 1 t]
  rw [hg_periodic.intervalIntegral_add_eq (ψ 0) 0, zero_add]
  simp only [g, Function.comp_apply]

theorem mobiusTransform_tendsto_on_circle
    (z₀ : ℂ) (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) :
    ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc (0 : ℝ) (2 * π) →
      Filter.Tendsto (fun a => mobiusTransform a (circleMap 0 1 θ))
        (nhdsWithin z₀ (ball 0 1)) (nhds z₀) := by
  have hnorm : ‖z₀‖ = 1 := mem_sphere_zero_iff_norm.mp hz₀
  have hz₀_ne : z₀ ≠ 0 := by
    intro h; simp [h] at hnorm

  have hstar_mul : star z₀ * z₀ = 1 := by
    have hinv : (starRingEnd ℂ z₀) = z₀⁻¹ := (RCLike.inv_eq_conj hnorm).symm
    rw [starRingEnd_apply] at hinv
    rw [hinv]
    exact inv_mul_cancel₀ hz₀_ne

  have hbad : (circleMap 0 1 ⁻¹' {-z₀}).Countable :=
    (Set.countable_singleton _).preimage_circleMap 0 one_ne_zero
  filter_upwards [hbad.ae_notMem volume] with θ hθne _hθ_mem
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hθne
  set z := circleMap 0 1 θ

  have hzz₀_ne : z + z₀ ≠ 0 := by
    intro h; exact hθne (by linear_combination h)

  have hdenom_ne : starRingEnd ℂ z₀ * z + 1 ≠ 0 := by
    rw [starRingEnd_apply, show star z₀ * z + 1 = star z₀ * (z + z₀) from by
      rw [mul_add, hstar_mul]]
    exact mul_ne_zero (by rwa [ne_eq, star_eq_zero]) hzz₀_ne

  have hval : mobiusTransform z₀ z = z₀ := by
    simp only [mobiusTransform, starRingEnd_apply]
    rw [show star z₀ * z + 1 = star z₀ * (z + z₀) from by rw [mul_add, hstar_mul]]
    rw [div_mul_eq_div_div_swap, div_self hzz₀_ne, one_div]
    have h_inv : z₀⁻¹ = star z₀ := by
      rw [RCLike.inv_eq_conj hnorm, starRingEnd_apply]
    rw [← h_inv, inv_inv]

  have hcont : ContinuousAt (fun a => mobiusTransform a z) z₀ := by
    show ContinuousAt (fun a => (z + a) / (starRingEnd ℂ a * z + 1)) z₀
    apply ContinuousAt.div
    · exact continuousAt_const.add continuousAt_id
    · have : ContinuousAt (fun a => star a * z + 1) z₀ :=
        (continuous_star.continuousAt.mul continuousAt_const).add continuousAt_const
      simp only [← starRingEnd_apply] at this
      exact this
    · exact hdenom_ne
  rw [show nhds z₀ = nhds (mobiusTransform z₀ z) from congr_arg nhds hval.symm]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem circleAverage_mobiusTransform_aestronglyMeasurable
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (z₀ : ℂ) (_hz₀ : z₀ ∈ sphere (0 : ℂ) 1) :
    ∀ᶠ a in nhdsWithin z₀ (ball 0 1),
      AEStronglyMeasurable (fun θ => U (mobiusTransform a (circleMap 0 1 θ)))
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * π))) := by
  apply Filter.Eventually.mono (eventually_of_mem self_mem_nhdsWithin (fun a ha => ha))
  intro a ha
  set ψ := invMobiusAngle a ha
  set g : ℝ → ℝ := fun t => U (mobiusTransform a (circleMap 0 1 t))

  have hg_periodic : Function.Periodic g (2 * π) := by
    intro t; show U (mobiusTransform a (circleMap 0 1 (t + 2 * π))) =
      U (mobiusTransform a (circleMap 0 1 t)); rw [periodic_circleMap 0 1 t]

  have hgψ : ∀ θ, (g ∘ ψ) θ = U (circleMap 0 1 θ) := by
    intro θ; simp only [Function.comp_apply, g]; rw [invMobiusAngle_mobiusTransform]

  have hψ_cont : ContinuousOn ψ (Set.uIcc 0 (2 * π)) :=
    (continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_invMobiusAngle a ha x).continuousAt)).continuousOn

  have hprod : IntervalIntegrable
      (fun θ => poissonKernel 0 a (circleMap 0 1 θ) • (g ∘ ψ) θ) volume 0 (2 * π) := by
    simp_rw [smul_eq_mul, hgψ]
    have hP_cont : ContinuousOn (fun θ => poissonKernel 0 a (circleMap 0 1 θ))
        (Set.uIcc 0 (2 * π)) := by
      apply ContinuousOn.mono (Continuous.continuousOn _) (Set.subset_univ _)
      simp only [poissonKernel_def, sub_zero]
      apply Continuous.div
      · exact ((continuous_norm.comp (continuous_circleMap 0 1)).pow 2).sub continuous_const
      · exact (continuous_norm.comp ((continuous_circleMap 0 1).sub continuous_const)).pow 2
      · intro θ
        apply pow_ne_zero 2; rw [norm_ne_zero_iff]
        intro heq
        have ha' := sub_eq_zero.mp heq
        have hn := norm_circleMap_zero_one θ
        rw [ha'] at hn
        rw [mem_ball, dist_zero_right] at ha; linarith
    exact hU.continuousOn_mul hP_cont

  have hg_ii_shifted : IntervalIntegrable g volume (ψ 0) (ψ (2 * π)) := by
    rw [← intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg hψ_cont
      (fun x _ => hasDerivAt_invMobiusAngle a ha x)
      (fun x _ => poissonKernel_nonneg_circleMap a ha x)]
    exact hprod

  have hψ_shift : ψ (2 * π) = ψ 0 + 2 * π := by
    have := invMobiusAngle_add_two_pi a ha 0; simp only [zero_add] at this; exact this
  rw [hψ_shift] at hg_ii_shifted

  have hg_ii : IntervalIntegrable g volume 0 (2 * π) := by
    have := (@Function.Periodic.intervalIntegrable_iff _ _ g (2 * π) (ψ 0) 0
      hg_periodic).mp hg_ii_shifted
    simpa using this

  rw [show Set.uIoc (0 : ℝ) (2 * π) = Set.Ioc 0 (2 * π) from Set.uIoc_of_le (by positivity)]
  exact hg_ii.aestronglyMeasurable

theorem circleAverage_mobiusTransform_bound
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (hUbd : ∃ M : ℝ, ∀ z, ‖U z‖ ≤ M)
    (z₀ : ℂ) (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) :
    ∃ bound : ℝ → ℝ,
      IntervalIntegrable bound MeasureTheory.volume (0 : ℝ) (2 * π) ∧
      ∀ᶠ a in nhdsWithin z₀ (ball 0 1),
        ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc (0 : ℝ) (2 * π) →
          ‖U (mobiusTransform a (circleMap 0 1 θ))‖ ≤ bound θ := by
  obtain ⟨M, hM⟩ := hUbd
  exact ⟨fun _ => M, intervalIntegrable_const,
    Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ _ => hM _))⟩

theorem circleAverage_mobiusTransform_tendsto
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (hUbd : ∃ M : ℝ, ∀ z, ‖U z‖ ≤ M)
    (z₀ : ℂ) (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) (hcont : ContinuousAt U z₀) :
    Filter.Tendsto (fun a => Real.circleAverage (U ∘ mobiusTransform a) 0 1)
      (nhdsWithin z₀ (ball 0 1)) (nhds (U z₀)) := by

  simp only [Real.circleAverage_def, Function.comp_def]


  have h_ptwise := mobiusTransform_tendsto_on_circle z₀ hz₀
  obtain ⟨bound, h_bound_int, h_bound⟩ := circleAverage_mobiusTransform_bound U hU hUbd z₀ hz₀
  have h_meas := circleAverage_mobiusTransform_aestronglyMeasurable U hU z₀ hz₀

  have h_lim : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc (0 : ℝ) (2 * π) →
      Filter.Tendsto (fun a => U (mobiusTransform a (circleMap 0 1 θ)))
        (nhdsWithin z₀ (ball 0 1)) (nhds (U z₀)) := by
    filter_upwards [h_ptwise] with θ hθ hθ_mem
    exact hcont.tendsto.comp (hθ hθ_mem)

  have h_integral_tendsto := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    bound h_meas h_bound h_bound_int h_lim


  have h_const_integral : ∫ θ in (0 : ℝ)..2 * π, U z₀ = 2 * π * U z₀ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

  rw [h_const_integral] at h_integral_tendsto
  have h_smul_tendsto : Filter.Tendsto
    (fun a => (2 * (π : ℝ))⁻¹ • ∫ θ in (0 : ℝ)..2 * π, U (mobiusTransform a (circleMap 0 1 θ)))
    (nhdsWithin z₀ (ball 0 1)) (nhds ((2 * π)⁻¹ • (2 * π * U z₀))) :=
    h_integral_tendsto.const_smul _
  rwa [show (2 * (π : ℝ))⁻¹ • (2 * π * U z₀) = U z₀ from by
    rw [smul_eq_mul, inv_mul_cancel_left₀ (by positivity)]] at h_smul_tendsto

theorem poissonIntegral_tendsto_boundary
    (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (hUbd : ∃ M : ℝ, ∀ z, ‖U z‖ ≤ M)
    (z₀ : ℂ) (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) (hcont : ContinuousAt U z₀) :
    Filter.Tendsto (poissonIntegral U) (nhdsWithin z₀ (ball 0 1)) (nhds (U z₀)) := by


  apply (circleAverage_mobiusTransform_tendsto U hU hUbd z₀ hz₀ hcont).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (poissonIntegral_eq_circleAverage_mobiusTransform U hU a ha).symm

end PoissonIntegralSetup

lemma harmonicOnNhd_congr_eqOn {f g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hf : HarmonicOnNhd f s) (heq : Set.EqOn f g s) : HarmonicOnNhd g s := by
  intro x hx
  have hfx := hf x hx
  have hev : f =ᶠ[nhds x] g :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, heq⟩
  exact ⟨hfx.1.congr_of_eventuallyEq hev.symm,
         (laplacian_congr_nhds hev).symm.trans hfx.2⟩

theorem schwarz_poisson_harmonic (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1) :
    IsHarmonic (poissonIntegral U) (ball 0 1) := by

  have hDiff := herglotzIntegral_differentiableOn U hU

  have hHarm := harmonicOnNhd_re_of_differentiableOn isOpen_ball hDiff


  exact harmonicOnNhd_congr_eqOn isOpen_ball hHarm
    (fun a ha ↦ (poissonIntegral_eq_re_herglotzIntegral U hU a ha).symm)

theorem schwarz_poisson_boundary (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (hUbd : ∃ M : ℝ, ∀ z, ‖U z‖ ≤ M)
    (z₀ : ℂ) (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) (hcont : ContinuousAt U z₀) :
    Filter.Tendsto (poissonIntegral U) (nhdsWithin z₀ (ball 0 1)) (nhds (U z₀)) :=
  poissonIntegral_tendsto_boundary U hU hUbd z₀ hz₀ hcont

theorem schwarz_poisson (U : ℂ → ℝ) (hU : CircleIntegrable U 0 1)
    (hUbd : ∃ M : ℝ, ∀ z, ‖U z‖ ≤ M) :

    IsHarmonic (poissonIntegral U) (ball 0 1) ∧

    ∀ z₀ ∈ sphere (0 : ℂ) 1, ContinuousAt U z₀ →
      Filter.Tendsto (poissonIntegral U) (nhdsWithin z₀ (ball 0 1)) (nhds (U z₀)) :=
  ⟨schwarz_poisson_harmonic U hU,
   fun z₀ hz₀ hcont ↦ schwarz_poisson_boundary U hU hUbd z₀ hz₀ hcont⟩





theorem IsHarmonic.mean_value_property {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hu : IsHarmonic u Ω) (hr : 0 ≤ r) (hdisk : closedBall z₀ r ⊆ Ω) :
    u z₀ = Real.circleAverage u z₀ r := by

  have hu_disk : IsHarmonic u (closedBall z₀ r) := hu.mono hdisk

  have hr_abs : |r| = r := abs_of_nonneg hr
  rw [← hr_abs] at hu_disk

  exact (HarmonicOnNhd.circleAverage_eq hu_disk).symm

set_option maxHeartbeats 1600000 in
theorem circleAverage_hasDerivAt_first
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    HasDerivAt (fun s => circleAverage u z₀ s)
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))) r₀ := by

  show HasDerivAt (fun s => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, u (circleMap z₀ s θ)) _ r₀
  suffices h : HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * π, u (circleMap z₀ s θ))
      (∫ θ in (0 : ℝ)..2 * π, (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))) r₀ by
    exact h.const_smul (2 * π)⁻¹

  set K := {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}
  have hK_compact : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall z₀ r₂)
    · exact (isClosed_le continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))).inter
        (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
    · intro z ⟨_, h2⟩; exact mem_closedBall.mpr (by rwa [dist_comm, dist_eq_norm, norm_sub_rev])
  have hK_sub : K ⊆ Ω := fun z ⟨h1, h2⟩ => hannulus z h1 h2
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK_compact.exists_thickening_subset_open hΩ hK_sub
  have hr0_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0

  have hmem_K : ∀ θ, circleMap z₀ r₀ θ ∈ K := fun θ =>
    ⟨by rw [circleMap_sub_center]; simp [abs_of_pos hr0_pos]; exact hr0,
     by rw [circleMap_sub_center]; simp [abs_of_pos hr0_pos]; exact hr0'⟩

  have hK2_sub_Ω : cthickening (δ / 2) K ⊆ Ω :=
    (cthickening_subset_thickening' hδ_pos (by linarith) K).trans hδ_sub

  have hmem_cthick : ∀ x ∈ ball r₀ (δ / 2), ∀ θ,
      circleMap z₀ x θ ∈ cthickening (δ / 2) K := by
    intro x hx θ
    apply mem_cthickening_of_dist_le _ (circleMap z₀ r₀ θ) _ _ (hmem_K θ)
    simp only [circleMap, dist_eq_norm]
    rw [show z₀ + ↑x * exp (↑θ * I) - (z₀ + ↑r₀ * exp (↑θ * I)) =
      (↑x - ↑r₀) * exp (↑θ * I) by ring,
      Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (by rwa [mem_ball, Real.dist_eq] at hx)
  have hmem_Ω : ∀ x ∈ ball r₀ (δ / 2), ∀ θ, circleMap z₀ x θ ∈ Ω := fun x hx θ =>
    hK2_sub_Ω (hmem_cthick x hx θ)

  have hu_C2 : ContDiffOn ℝ 2 u Ω := hu.contDiffOn
  have hu_cont : ContinuousOn u Ω := hu_C2.continuousOn
  have hfderiv_cont : ContinuousOn (fderiv ℝ u) Ω :=
    hu_C2.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hu_diff : ∀ z ∈ Ω, DifferentiableAt ℝ u z := fun z hz =>
    (hu_C2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (hΩ.mem_nhds hz)

  obtain ⟨M, hM⟩ := (hK_compact.cthickening (r := δ / 2)).exists_bound_of_continuousOn
    (hfderiv_cont.mono hK2_sub_Ω)

  have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (a := 0) (b := 2 * π) (μ := MeasureTheory.MeasureSpace.volume)
    (bound := fun _ => M)
    (F := fun s θ => u (circleMap z₀ s θ))
    (F' := fun s θ => (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
    (x₀ := r₀) (s := ball r₀ (δ / 2))
    (ball_mem_nhds r₀ (by linarith))

    (by apply eventually_of_mem (ball_mem_nhds r₀ (by linarith : δ / 2 > 0))
        intro x hx
        exact (hu_cont.comp_continuous (continuous_circleMap z₀ x)
          (hmem_Ω x hx)).aestronglyMeasurable)

    ((hu_cont.comp_continuous (continuous_circleMap z₀ r₀)
      (fun θ => hK_sub (hmem_K θ))).intervalIntegrable 0 _)

    (by have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ r₀ θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).aestronglyMeasurable)

    (by apply Eventually.of_forall; intro t _ x hx
        calc ‖(fderiv ℝ u (circleMap z₀ x t)) (exp (↑t * I))‖
            ≤ ‖fderiv ℝ u (circleMap z₀ x t)‖ * ‖exp (↑t * I)‖ :=
              (fderiv ℝ u (circleMap z₀ x t)).le_opNorm _
          _ = ‖fderiv ℝ u (circleMap z₀ x t)‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ M := hM _ (hmem_cthick x hx t))

    intervalIntegrable_const

    (by apply Eventually.of_forall; intro t _ x hx
        exact (hu_diff _ (hmem_Ω x hx t)).hasFDerivAt.comp_hasDerivAt x (by
          have : HasDerivAt (fun R : ℝ => z₀ + (R : ℂ) * exp (↑t * I))
              (exp (↑t * I)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
              (exp (↑t * I))).const_add z₀
          convert this using 1))
  exact leibniz.2

theorem circleAverage_hasDerivAt_second
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    let V' := fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r θ)) (exp (↑θ * I))
    HasDerivAt V'
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))) r₀ := by
  intro V'

  suffices h : HasDerivAt (fun s => ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
      (∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))) r₀ by
    exact h.const_smul (2 * π)⁻¹

  set K := {z : ℂ | r₁ ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r₂}
  have hK_compact : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_closedBall z₀ r₂)
    · exact (isClosed_le continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))).inter
        (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
    · intro z ⟨_, h2⟩; exact mem_closedBall.mpr (by rwa [dist_comm, dist_eq_norm, norm_sub_rev])
  have hK_sub : K ⊆ Ω := fun z ⟨h1, h2⟩ => hannulus z h1 h2
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hK_compact.exists_thickening_subset_open hΩ hK_sub
  have hr0_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0

  have hmem_K : ∀ θ, circleMap z₀ r₀ θ ∈ K := fun θ =>
    ⟨by rw [circleMap_sub_center]; simp [abs_of_pos hr0_pos]; exact hr0,
     by rw [circleMap_sub_center]; simp [abs_of_pos hr0_pos]; exact hr0'⟩

  have hK2_sub_Ω : cthickening (δ / 2) K ⊆ Ω :=
    (cthickening_subset_thickening' hδ_pos (by linarith) K).trans hδ_sub

  have hmem_cthick : ∀ x ∈ ball r₀ (δ / 2), ∀ θ,
      circleMap z₀ x θ ∈ cthickening (δ / 2) K := by
    intro x hx θ
    apply mem_cthickening_of_dist_le _ (circleMap z₀ r₀ θ) _ _ (hmem_K θ)
    simp only [circleMap, dist_eq_norm]
    rw [show z₀ + ↑x * exp (↑θ * I) - (z₀ + ↑r₀ * exp (↑θ * I)) =
      (↑x - ↑r₀) * exp (↑θ * I) by ring,
      Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_of_lt (by rwa [mem_ball, Real.dist_eq] at hx)
  have hmem_Ω : ∀ x ∈ ball r₀ (δ / 2), ∀ θ, circleMap z₀ x θ ∈ Ω := fun x hx θ =>
    hK2_sub_Ω (hmem_cthick x hx θ)

  have hu_C2 : ContDiffOn ℝ 2 u Ω := hu.contDiffOn
  have hfderiv_cont : ContinuousOn (fderiv ℝ u) Ω :=
    hu_C2.continuousOn_fderiv_of_isOpen hΩ (by norm_num)

  have hfderiv_C1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω :=
    hu_C2.fderiv_of_isOpen hΩ (by norm_num)

  have hfderiv2_cont : ContinuousOn (fderiv ℝ (fderiv ℝ u)) Ω :=
    hfderiv_C1.continuousOn_fderiv_of_isOpen hΩ (by norm_num)

  have hg_diff : ∀ z ∈ Ω, ∀ v : ℂ, DifferentiableAt ℝ (fun w => (fderiv ℝ u w) v) z :=
    fun z hz v =>
      ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp_contDiffOn hfderiv_C1).differentiableOn
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt (hΩ.mem_nhds hz)

  obtain ⟨M, hM⟩ := (hK_compact.cthickening (r := δ / 2)).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ u)) (hfderiv2_cont.mono hK2_sub_Ω)


  have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (a := 0) (b := 2 * π) (μ := MeasureTheory.MeasureSpace.volume)
    (bound := fun _ => M)
    (F := fun s θ => (fderiv ℝ u (circleMap z₀ s θ)) (exp (↑θ * I)))
    (F' := fun s θ => (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I)))
        (circleMap z₀ s θ)) (exp (↑θ * I)))
    (x₀ := r₀) (s := ball r₀ (δ / 2))
    (ball_mem_nhds r₀ (by linarith))

    (by apply eventually_of_mem (ball_mem_nhds r₀ (by linarith : δ / 2 > 0))
        intro x hx
        have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ x θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ x) (fun θ => hmem_Ω x hx θ)
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).aestronglyMeasurable)

    (by have h1 : Continuous (fun θ => fderiv ℝ u (circleMap z₀ r₀ θ)) :=
          hfderiv_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have h2 : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop
        exact ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (h1.prodMk h2)).intervalIntegrable 0 _)

    (by


        have hfdu_diff_at : ∀ z ∈ Ω, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
          (hfderiv_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
            (hΩ.mem_nhds hz)


        suffices Continuous (fun θ => (fderiv ℝ (fun z => (fderiv ℝ u z)
            (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I))) by
          exact this.aestronglyMeasurable

        have hrewrite : ∀ θ, fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I)))
            (circleMap z₀ r₀ θ) =
            (ContinuousLinearMap.apply ℝ ℝ (exp (↑θ * I))).comp
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) := by
          intro θ
          exact ((ContinuousLinearMap.apply ℝ ℝ (exp (↑θ * I))).hasFDerivAt.comp
            (circleMap z₀ r₀ θ) (hfdu_diff_at _ (hK_sub (hmem_K θ))).hasFDerivAt).fderiv

        simp_rw [hrewrite, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

        have hA : Continuous (fun θ => fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) :=
          hfderiv2_cont.comp_continuous (continuous_circleMap z₀ r₀) (fun θ => hK_sub (hmem_K θ))
        have hB : Continuous (fun θ : ℝ => exp ((θ : ℂ) * I)) := by fun_prop

        exact (((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp
          (((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp (hA.prodMk hB)).prodMk hB))))

    (by apply Eventually.of_forall; intro t _ x hx

        show ‖(fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑t * I))) (circleMap z₀ x t))
            (exp (↑t * I))‖ ≤ M
        have hfdu_diff_at : DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ x t) :=
          (hfderiv_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
            (hΩ.mem_nhds (hmem_Ω x hx t))
        have hkey : HasFDerivAt (fun z => (fderiv ℝ u z) (exp (↑t * I)))
            ((ContinuousLinearMap.apply ℝ ℝ (exp (↑t * I))).comp
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t))) (circleMap z₀ x t) := by
          show HasFDerivAt ((fun g => g (exp (↑t * I))) ∘ fderiv ℝ u) _ _
          exact (ContinuousLinearMap.apply ℝ ℝ (exp (↑t * I))).hasFDerivAt.comp
            (circleMap z₀ x t) hfdu_diff_at.hasFDerivAt
        rw [hkey.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        calc ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I)) (exp (↑t * I))‖
            ≤ ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))‖ *
              ‖exp (↑t * I)‖ :=
              ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))).le_opNorm _
          _ = ‖(fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)) (exp (↑t * I))‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ ‖fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)‖ * ‖exp (↑t * I)‖ :=
              (fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)).le_opNorm _
          _ = ‖fderiv ℝ (fderiv ℝ u) (circleMap z₀ x t)‖ := by
              rw [Complex.norm_exp_ofReal_mul_I, mul_one]
          _ ≤ M := hM _ (hmem_cthick x hx t))


    intervalIntegrable_const

    (by apply Eventually.of_forall; intro t _ x hx
        exact (hg_diff _ (hmem_Ω x hx t) (exp (↑t * I))).hasFDerivAt.comp_hasDerivAt x (by
          have : HasDerivAt (fun R : ℝ => z₀ + (R : ℂ) * exp (↑t * I))
              (exp (↑t * I)) x := by
            simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
              (exp (↑t * I))).const_add z₀
          convert this using 1))
  exact leibniz.2

lemma bilinear_trace_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z : ℂ) :
    B z z + B (I * z) (I * z) = (z.re ^ 2 + z.im ^ 2) * (B 1 1 + B I I) := by
  set a := z.re; set b := z.im
  have hz : z = (a : ℝ) • (1 : ℂ) + (b : ℝ) • (I : ℂ) := by
    apply Complex.ext <;> simp [a, b]
  have hiz : I * z = (-(b : ℝ)) • (1 : ℂ) + (a : ℝ) • (I : ℂ) := by
    apply Complex.ext <;> simp [a, b, mul_comm]
  conv_lhs =>
    rw [hz]
    rw [show I * ((a : ℝ) • (1 : ℂ) + (b : ℝ) • (I : ℂ)) =
        (-(b : ℝ)) • (1 : ℂ) + (a : ℝ) • (I : ℂ) from by rw [← hz]; exact hiz]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp; ring

lemma harmonic_fderiv_trace_zero {u : ℂ → ℝ} {z : ℂ} (h : HarmonicAt u z) :
    (fderiv ℝ (fderiv ℝ u) z) 1 1 + (fderiv ℝ (fderiv ℝ u) z) I I = 0 := by
  have hΔ : (Laplacian.laplacian u) z = 0 := h.2.eq_of_nhds
  have hformula := laplacian_eq_iteratedFDeriv_orthonormalBasis u Complex.orthonormalBasisOneI
  rw [hformula] at hΔ
  simp only [Fin.sum_univ_two] at hΔ
  have hv0 : (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 0 = 1 :=
    by simp [show (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 0 = (![1, I] : Fin 2 → ℂ) 0 from
      congr_fun Complex.coe_orthonormalBasisOneI 0]
  have hv1 : (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 1 = I :=
    by simp [show (Complex.orthonormalBasisOneI : Fin 2 → ℂ) 1 = (![1, I] : Fin 2 → ℂ) 1 from
      congr_fun Complex.coe_orthonormalBasisOneI 1]
  rw [hv0, hv1] at hΔ
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv] at hΔ
  exact hΔ

lemma harmonic_second_deriv_neg {u : ℂ → ℝ} {z e : ℂ} (h : HarmonicAt u z)
    (he : e.re ^ 2 + e.im ^ 2 = 1) :
    (fderiv ℝ (fderiv ℝ u) z) e e = -(fderiv ℝ (fderiv ℝ u) z) (I * e) (I * e) := by
  have := bilinear_trace_rotation (fderiv ℝ (fderiv ℝ u) z) e
  rw [he, one_mul] at this
  linarith [this, harmonic_fderiv_trace_zero h]

lemma cexp_re_sq_add_im_sq (θ : ℝ) :
    (cexp (↑θ * I)).re ^ 2 + (cexp (↑θ * I)).im ^ 2 = 1 := by
  rw [exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

theorem periodicity_of_circle_derivative
    {u : ℂ → ℝ} {z₀ : ℂ} {r₀ : ℝ}
    (hu_C2 : ∀ θ : ℝ, ContDiffAt ℝ 2 u (circleMap z₀ r₀ θ)) :
    r₀ * ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I)) =
      ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I)) := by

  have hDu_cont : Continuous (fun (t : ℝ) => fderiv ℝ u (circleMap z₀ r₀ t)) := by
    apply continuous_iff_continuousAt.mpr; intro t
    exact ((hu_C2 t).fderiv_right (m := 1) le_rfl).continuousAt.comp
      (continuous_circleMap z₀ r₀).continuousAt
  have hD2u_cont : Continuous (fun (t : ℝ) => fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) := by
    apply continuous_iff_continuousAt.mpr; intro t
    exact ((hu_C2 t).fderiv_right (m := 1) le_rfl |>.fderiv_right (m := 0)
      le_rfl).continuousAt.comp (continuous_circleMap z₀ r₀).continuousAt
  have hIexp_cont : Continuous (fun (t : ℝ) => I * exp ((↑t : ℂ) * I)) := by fun_prop
  have hexp_cont : Continuous (fun (t : ℝ) => exp ((↑t : ℂ) * I)) := by fun_prop

  have hA_int : IntervalIntegrable (fun (t : ℝ) =>
      r₀ * (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (I * exp (↑t * I)) (I * exp (↑t * I)))
      volume 0 (2 * π) :=
    (((hD2u_cont.clm_apply hIexp_cont).clm_apply hIexp_cont).const_mul r₀).intervalIntegrable 0 _
  have hB_int : IntervalIntegrable (fun (t : ℝ) =>
      (fderiv ℝ u (circleMap z₀ r₀ t)) (exp (↑t * I))) volume 0 (2 * π) :=
    (hDu_cont.clm_apply hexp_cont).intervalIntegrable 0 _

  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun (s : ℝ) => (fderiv ℝ u (circleMap z₀ r₀ s)) (I * exp (↑s * I)))
      (r₀ * (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (I * exp (↑t * I)) (I * exp (↑t * I))
       - (fderiv ℝ u (circleMap z₀ r₀ t)) (exp (↑t * I))) t := by
    intro t _
    have hDu_diff : DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ r₀ t) :=
      ((hu_C2 t).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
    have hcircle := hasDerivAt_circleMap z₀ r₀ t
    have hc : HasDerivAt (fun (s : ℝ) => fderiv ℝ u (circleMap z₀ r₀ s))
        ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ t)) (circleMap 0 r₀ t * I)) t :=
      hDu_diff.hasFDerivAt.comp_hasDerivAt t hcircle
    have he : HasDerivAt (fun (s : ℝ) => exp ((↑s : ℂ) * I)) (exp ((↑t : ℂ) * I) * I) t := by
      have h1 := ((ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp
      simp only [ofRealCLM_apply, ofReal_one, one_mul] at h1; exact h1
    have hv : HasDerivAt (fun (s : ℝ) => I * exp ((↑s : ℂ) * I))
        (I * (exp ((↑t : ℂ) * I) * I)) t := he.const_mul I
    refine (hc.clm_apply hv).congr_deriv ?_
    set e := exp ((↑t : ℂ) * I)
    have h1 : circleMap 0 r₀ t * I = r₀ • (I * e) := by
      rw [circleMap_zero, Complex.real_smul]; ring
    rw [h1]; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h3 : I * (e * I) = (-1 : ℝ) • e := by
      simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_one]
      ring_nf; rw [I_sq]; ring
    rw [h3, map_smul, smul_eq_mul]; ring

  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hA_int.sub hB_int)

  have hper : (fderiv ℝ u (circleMap z₀ r₀ (2 * π))) (I * exp (↑(2 * π) * I)) =
      (fderiv ℝ u (circleMap z₀ r₀ 0)) (I * exp (↑(0 : ℝ) * I)) := by
    have hcm : circleMap z₀ r₀ (2 * π) = circleMap z₀ r₀ 0 := by
      have := periodic_circleMap z₀ r₀ 0; simp at this; exact this
    have hexp : exp ((↑(2 * π) : ℂ) * I) = exp ((↑(0 : ℝ) : ℂ) * I) := by
      have h := exp_mul_I_periodic (0 : ℂ)
      simp only [zero_add, ofReal_zero, zero_mul, Complex.exp_zero] at h ⊢
      push_cast; exact h
    rw [hcm, hexp]
  rw [hper, sub_self] at hftc

  rw [intervalIntegral.integral_sub hA_int hB_int] at hftc
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

lemma fderiv_eval_eq_fderiv2 {u : ℂ → ℝ} {z₀ v w : ℂ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) z₀) :
    (fderiv ℝ (fun z => (fderiv ℝ u z) v) z₀) w =
    (fderiv ℝ (fderiv ℝ u) z₀) w v := by
  have hL : HasFDerivAt (fun z => (fderiv ℝ u z) v)
    ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ u) z₀)) z₀ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp z₀ hu.hasFDerivAt
  rw [hL.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

theorem euler_ode_from_laplacian
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ r₀ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr0 : r₁ ≤ r₀) (hr0' : r₀ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    let V'₀ := (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ u (circleMap z₀ r₀ θ)) (exp (↑θ * I))
    let V''₀ := (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
        (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ))
          (exp (↑θ * I))
    V''₀ + V'₀ / r₀ = 0 := by

  have hr₀_pos : 0 < r₀ := lt_of_lt_of_le hr₁ hr0

  have hC2 : ∀ θ : ℝ, ContDiffAt ℝ 2 u (circleMap z₀ r₀ θ) := by
    intro θ
    have h_in_Ω : circleMap z₀ r₀ θ ∈ Ω := by
      apply hannulus
      · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
      · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
    exact (hu.harmonicAt h_in_Ω).1

  have hdiff2 : ∀ θ : ℝ, DifferentiableAt ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ) := by
    intro θ; exact (hC2 θ).fderiv_right le_rfl |>.differentiableAt one_ne_zero

  have hharm : ∀ θ : ℝ, HarmonicAt u (circleMap z₀ r₀ θ) := by
    intro θ
    apply hu.harmonicAt
    apply hannulus
    · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith
    · rw [circleMap_sub_center]; simp [abs_of_pos hr₀_pos]; linarith


  have hV''_eq : ∀ θ : ℝ,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) =
      (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) (exp (↑θ * I)) :=
    fun θ => fderiv_eval_eq_fderiv2 (hdiff2 θ)

  have hharm_neg : ∀ θ : ℝ,
      (fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) (exp (↑θ * I)) =
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I))) := by
    intro θ
    exact harmonic_second_deriv_neg (hharm θ) (cexp_re_sq_add_im_sq θ)

  have hV''_neg : ∀ θ : ℝ,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r₀ θ)) (exp (↑θ * I)) =
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * exp (↑θ * I)) (I * exp (↑θ * I))) :=
    fun θ => (hV''_eq θ).trans (hharm_neg θ)

  simp only [hV''_neg]

  have hperiod := periodicity_of_circle_derivative hC2

  have hint_neg : (∫ θ in (0:ℝ)..2 * π,
      -((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * cexp (↑θ * I)))
        (I * cexp (↑θ * I))) =
      -(∫ θ in (0:ℝ)..2 * π,
        ((fderiv ℝ (fderiv ℝ u) (circleMap z₀ r₀ θ)) (I * cexp (↑θ * I)))
          (I * cexp (↑θ * I))) := intervalIntegral.integral_neg
  rw [hint_neg]
  simp only [smul_eq_mul]
  rw [← hperiod]
  have hr_ne : r₀ ≠ 0 := ne_of_gt hr₀_pos
  field_simp
  ring

theorem harmonic_circleAverage_euler_ode
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ V' V'' : ℝ → ℝ,
      (∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt (fun s => circleAverage u z₀ s) (V' r) r) ∧
      (∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V' (V'' r) r) ∧
      (∀ r, r₁ ≤ r → r ≤ r₂ → V'' r + V' r / r = 0) := by

  refine ⟨fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ u (circleMap z₀ r θ)) (exp (↑θ * I)),
    fun r => (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
      (fderiv ℝ (fun z => (fderiv ℝ u z) (exp (↑θ * I))) (circleMap z₀ r θ))
        (exp (↑θ * I)),
    ?_, ?_, ?_⟩

  · intro r hr hr2
    exact circleAverage_hasDerivAt_first hu hΩ hr₁ hr₁₂ hr hr2 hannulus

  · intro r hr hr2
    exact circleAverage_hasDerivAt_second hu hΩ hr₁ hr₁₂ hr hr2 hannulus

  · intro r hr hr2
    exact euler_ode_from_laplacian hu hΩ hr₁ hr₁₂ hr hr2 hannulus

theorem euler_ode_solution
    (V : ℝ → ℝ) (V' V'' : ℝ → ℝ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁)
    (hV : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V (V' r) r)
    (hV' : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V' (V'' r) r)
    (hode : ∀ r, r₁ ≤ r → r ≤ r₂ → V'' r + V' r / r = 0) :
    ∃ α : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt V (α / r) r := by

  set W := fun r => r * V' r
  have hW_deriv : ∀ r, r₁ ≤ r → r ≤ r₂ → HasDerivAt W 0 r := by
    intro r hr1 hr2
    have hd1 : HasDerivAt (fun s => s) 1 r := hasDerivAt_id r
    have hd2 : HasDerivAt V' (V'' r) r := hV' r hr1 hr2
    have hd3 : HasDerivAt W (1 * V' r + r * V'' r) r := hd1.mul hd2
    have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hr1)
    have hV''_val : V'' r = -(V' r / r) := by linarith [hode r hr1 hr2]
    have key : V' r + r * V'' r = 0 := by
      rw [hV''_val, mul_neg, mul_div_cancel₀ _ hr_ne]; linarith
    simp only [one_mul] at hd3
    rwa [show (0 : ℝ) = V' r + r * V'' r from key.symm]

  have hW_cont : ContinuousOn W (Icc r₁ r₂) :=
    fun x hx => (hW_deriv x hx.1 hx.2).continuousAt.continuousWithinAt
  have hW_const : ∀ r, r₁ ≤ r → r ≤ r₂ → W r = W r₁ := by
    intro r hr1 hr2
    exact eq_of_has_deriv_right_eq
      (fun x hx => (hW_deriv x hx.1 (le_of_lt hx.2)).hasDerivWithinAt)
      (fun x _ => hasDerivWithinAt_const x _ _)
      hW_cont continuousOn_const rfl r ⟨hr1, hr2⟩

  use W r₁
  intro r hr1 hr2
  have hW_eq : W r = W r₁ := hW_const r hr1 hr2
  have hr_ne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hr1)
  have hVr : V' r = W r₁ / r := by
    have : r * V' r = W r₁ := hW_eq
    field_simp at this ⊢; linarith
  rw [show W r₁ / r = V' r from hVr.symm]
  exact hV r hr1 hr2

theorem harmonic_circleAverage_ode
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ α : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ →
      HasDerivAt (fun s => circleAverage u z₀ s) (α / r) r := by
  obtain ⟨V', V'', hV, hV', hode⟩ := harmonic_circleAverage_euler_ode hu hΩ hr₁ hr₁₂ hannulus
  exact euler_ode_solution _ V' V'' r₁ r₂ hr₁ hV hV' hode

theorem harmonic_annulus_mean_value
    {u : ℂ → ℝ} {Ω : Set ℂ} {z₀ : ℂ} {r₁ r₂ : ℝ}
    (hu : IsHarmonic u Ω) (hΩ : IsOpen Ω)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hannulus : ∀ z, r₁ ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r₂ → z ∈ Ω) :
    ∃ α β : ℝ, ∀ r, r₁ ≤ r → r ≤ r₂ →
      circleAverage u z₀ r = α * Real.log r + β := by

  obtain ⟨α, hode⟩ := harmonic_circleAverage_ode hu hΩ hr₁ hr₁₂ hannulus
  set V := fun s => circleAverage u z₀ s
  set g := fun s => α * Real.log s

  refine ⟨α, V r₁ - g r₁, ?_⟩
  intro r hr1 hr2
  suffices h : V r = g r + (V r₁ - g r₁) by linarith


  have hV_cont : ContinuousOn V (Icc r₁ r₂) :=
    fun x hx => (hode x hx.1 hx.2).continuousAt.continuousWithinAt
  have hg_cont : ContinuousOn g (Icc r₁ r₂) :=
    (continuousOn_const.mul (continuousOn_id.log fun x hx => ne_of_gt (lt_of_lt_of_le hr₁ hx.1)))
  have hgc_cont : ContinuousOn (fun s => g s + (V r₁ - g r₁)) (Icc r₁ r₂) :=
    hg_cont.add continuousOn_const
  have hV_deriv : ∀ x ∈ Ico r₁ r₂, HasDerivWithinAt V (α / x) (Ici x) x :=
    fun x hx => (hode x hx.1 (le_of_lt hx.2)).hasDerivWithinAt
  have hgc_deriv : ∀ x ∈ Ico r₁ r₂,
      HasDerivWithinAt (fun s => g s + (V r₁ - g r₁)) (α / x) (Ici x) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₁ hx.1)
    have hg_at : HasDerivAt g (α * x⁻¹) x := (hasDerivAt_log hxne).const_mul α
    have hconst_at : HasDerivAt (fun _ => V r₁ - g r₁) 0 x := hasDerivAt_const x _
    have h := hg_at.add hconst_at
    simp only [add_zero] at h
    rw [show α / x = α * x⁻¹ from div_eq_mul_inv α x]
    exact h.hasDerivWithinAt
  exact eq_of_has_deriv_right_eq hV_deriv hgc_deriv hV_cont hgc_cont (by ring) r ⟨hr1, hr2⟩
