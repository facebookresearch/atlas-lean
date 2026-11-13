/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Constructions

open Complex Nat Filter Topology MeasureTheory Set

theorem euler_product_riemannZeta_inv {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s)) := by
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  have hp := riemannZeta_eulerProduct_hasProd hs
  have hp_inv : HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))) (riemannZeta s)⁻¹ :=
    (hp.inv₀ hζ_ne).congr (fun S => by rw [Finset.prod_inv_distrib, inv_inv])
  exact hp_inv.tprod_eq.symm

namespace Newman

noncomputable section

set_option maxHeartbeats 800000 in
lemma left_semicircle_integral_tendsto
    (R : ℝ) (hR : 0 < R) (h : ℝ → ℂ)
    (hh_int : Integrable h (volume.restrict (Ioc (Real.pi / 2) (3 * Real.pi / 2))))
    (hh_meas : AEStronglyMeasurable h volume) :
    Tendsto (fun T : ℝ => ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
      Complex.exp (↑R * Complex.exp (↑θ * I) * ↑T) * h θ) atTop (𝓝 0) := by
  rw [show (0 : ℂ) = ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), (0 : ℂ) from by simp]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun θ => ‖h θ‖)
  ·
    exact Filter.Eventually.of_forall fun T => by
      apply AEStronglyMeasurable.mul _ (hh_meas.mono_measure Measure.restrict_le_self)
      exact Continuous.aestronglyMeasurable (by fun_prop)
  ·
    rw [Filter.eventually_atTop]
    exact ⟨0, fun T hT =>
      Filter.Eventually.of_forall fun θ hθ => by
        rw [uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 3 * Real.pi / 2)] at hθ
        rw [norm_mul]
        apply mul_le_of_le_one_left (norm_nonneg _)
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_lt hθ.1) (by linarith [hθ.2])
        have hre : (↑R * Complex.exp (↑θ * I) * ↑T).re = R * Real.cos θ * T := by simp
        rw [hre]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hR) hcos) hT⟩
  ·
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 3 * Real.pi / 2)]
    exact hh_int.norm
  ·
    rw [uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 3 * Real.pi / 2)]
    have key : ∀ θ ∈ Ioo (Real.pi / 2) (3 * Real.pi / 2),
        Tendsto (fun n : ℝ => Complex.exp (↑R * Complex.exp (↑θ * I) * ↑n) * h θ)
          atTop (𝓝 0) := by
      intro θ hθ
      have hcos := Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [hθ.2])
      rw [show (0 : ℂ) = 0 * h θ from by ring]
      apply Tendsto.mul_const
      rw [Complex.tendsto_exp_nhds_zero_iff]
      simp_rw [show ∀ T : ℝ, (↑R * Complex.exp (↑θ * I) * ↑T).re = R * Real.cos θ * T from
        fun T => by simp]
      have hneg : R * Real.cos θ < 0 := mul_neg_of_pos_of_neg hR hcos
      exact (tendsto_neg_atTop_atBot.comp
        (Tendsto.const_mul_atTop (neg_pos.mpr hneg) tendsto_id)).congr
          (fun T => by simp [neg_mul])

    rw [Filter.Eventually, mem_ae_iff]
    exact measure_mono_null (fun θ hθ => by
      rw [mem_compl_iff, mem_setOf_eq, Classical.not_imp] at hθ
      rw [mem_singleton_iff]; by_contra hne
      exact hθ.2 (key θ ⟨hθ.1.1, lt_of_le_of_ne hθ.1.2 hne⟩)) Real.volume_singleton

def truncatedLaplaceTransform (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-z * ↑t) * f t

lemma truncatedLaplaceTransform_zero (f : ℝ → ℂ) (T : ℝ) :
    truncatedLaplaceTransform f T 0 = ∫ t in (0 : ℝ)..T, f t := by
  unfold truncatedLaplaceTransform; congr 1; ext t; simp

lemma not_intervalIntegrable_exp_mul {f : ℝ → ℂ} {z : ℂ} {a b : ℝ}
    (hf : ¬IntervalIntegrable f volume a b) :
    ¬IntervalIntegrable (fun t => Complex.exp (-z * ↑t) * f t) volume a b := by
  intro hint; apply hf
  have hcont : ContinuousOn (fun t : ℝ => Complex.exp (z * ↑t)) (uIcc a b) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  convert hint.continuousOn_mul hcont using 1; ext t
  simp only [← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

lemma abs_le_abs_of_mem_uIoc {T t : ℝ} (ht : t ∈ uIoc 0 T) : |t| ≤ |T| := by
  simp only [uIoc, mem_Ioc] at ht
  rw [abs_le]
  exact ⟨by linarith [neg_abs_le T,
              le_min (by linarith [abs_nonneg T] : -|T| ≤ 0) (neg_abs_le T)],
         by linarith [max_le (abs_nonneg T) (le_abs_self T)]⟩

lemma norm_exp_mul_le {z z₀ : ℂ} {t T : ℝ} (hz : ‖z - z₀‖ ≤ 1) (ht : t ∈ uIoc 0 T)
    (f : ℝ → ℂ) :
    ‖Complex.exp (-z * ↑t) * f t‖ ≤ Real.exp ((‖z₀‖ + 1) * |T|) * ‖f t‖ := by
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hre : (-z * ↑t).re = -z.re * t := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  calc -z.re * t ≤ |(-z.re) * t| := le_abs_self _
    _ = |z.re| * |t| := by rw [abs_mul, abs_neg]
    _ ≤ ‖z‖ * |T| := by
        exact mul_le_mul (Complex.abs_re_le_norm z) (abs_le_abs_of_mem_uIoc ht)
          (abs_nonneg _) (norm_nonneg _)
    _ ≤ (‖z₀‖ + 1) * |T| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
          _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + 1 := by linarith

theorem truncatedLaplaceTransform_continuous (f : ℝ → ℂ) (T : ℝ) :
    Continuous (truncatedLaplaceTransform f T) := by
  unfold truncatedLaplaceTransform
  by_cases hf : IntervalIntegrable f volume 0 T
  ·
    apply continuous_iff_continuousAt.mpr
    intro z₀
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun t => Real.exp ((‖z₀‖ + 1) * |T|) * ‖f t‖)
    ·
      apply Eventually.of_forall
      intro z
      rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff]
      have hint : IntervalIntegrable (fun t => Complex.exp (-z * ↑t) * f t) volume 0 T :=
        hf.continuousOn_mul
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal)).continuousOn
      exact ⟨hint.1.aestronglyMeasurable, hint.2.aestronglyMeasurable⟩
    ·
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds z₀ one_pos, fun z hz => ?_⟩
      apply Eventually.of_forall
      intro t ht
      exact norm_exp_mul_le
        (by rw [Metric.mem_ball, Complex.dist_eq] at hz; exact le_of_lt hz) ht f
    ·
      exact hf.norm.const_mul _
    ·
      apply Eventually.of_forall
      intro t _
      exact ((Complex.continuous_exp.comp
        ((continuous_neg.comp continuous_id).mul continuous_const)).continuousAt).mul
        continuousAt_const
  ·
    have : (fun z => ∫ t in (0:ℝ)..T, Complex.exp (-z * ↑t) * f t) = fun _ => 0 := by
      ext z; exact intervalIntegral.integral_undef (not_intervalIntegrable_exp_mul hf)
    rw [this]; exact continuous_const

theorem newman_g_diffOn_closedBall
    (g : ℂ → ℂ) (R : ℝ) (_hR : 0 < R)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z) :
    DifferentiableOn ℂ g (Metric.closedBall 0 ↑R) :=
  fun z _ => (hg_diffAt z).differentiableWithinAt

theorem truncatedLaplaceTransform_differentiable
    (f : ℝ → ℂ) (T : ℝ) :
    Differentiable ℂ (truncatedLaplaceTransform f T) := by
  by_cases hf : IntervalIntegrable f volume 0 T
  ·
    intro z₀
    unfold truncatedLaplaceTransform
    let s := Metric.ball z₀ 1
    let F : ℂ → ℝ → ℂ := fun z t => Complex.exp (-z * ↑t) * f t
    let F' : ℂ → ℝ → ℂ := fun z t => -(↑t) * Complex.exp (-z * ↑t) * f t
    let bound : ℝ → ℝ := fun t => |t| * Real.exp ((‖z₀‖ + 1) * |t|) * ‖f t‖
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℂ) (μ := volume) (F := F) (F' := F') (a := 0) (b := T)
      (bound := bound) (x₀ := z₀) (s := s)
      ?hs ?hF_meas ?hF_int ?hF'_meas ?h_bound ?bound_integrable ?h_diff
    · exact key.2.differentiableAt
    case hs => exact Metric.ball_mem_nhds z₀ one_pos
    case hF_meas =>
      filter_upwards with z
      exact ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * ↑t))).aestronglyMeasurable).mul
        ((intervalIntegrable_iff.mp hf).aestronglyMeasurable)
    case hF_int =>
      exact hf.continuousOn_mul
        (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z₀ * ↑t))).continuousOn
    case hF'_meas =>
      exact (((by fun_prop : Continuous (fun t : ℝ => -(↑t : ℂ))).aestronglyMeasurable).mul
        (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z₀ * ↑t))).aestronglyMeasurable).mul
        ((intervalIntegrable_iff.mp hf).aestronglyMeasurable)
    case h_bound =>
      apply Filter.Eventually.of_forall
      intro t _ht x hx
      show ‖-(↑t : ℂ) * Complex.exp (-x * ↑t) * f t‖ ≤
        |t| * Real.exp ((‖z₀‖ + 1) * |t|) * ‖f t‖
      simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs]
      gcongr
      simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have hzb : ‖x‖ ≤ ‖z₀‖ + 1 := by
        linarith [norm_sub_norm_le x z₀, (dist_eq_norm x z₀ ▸ (Metric.mem_ball.mp hx)).le]
      calc -(x.re * t) ≤ |x.re * t| := neg_le_abs _
        _ = |x.re| * |t| := abs_mul x.re t
        _ ≤ ‖x‖ * |t| := by gcongr; exact Complex.abs_re_le_norm x
        _ ≤ (‖z₀‖ + 1) * |t| := by gcongr
    case bound_integrable =>
      exact (hf.norm).continuousOn_mul
        (by fun_prop : Continuous (fun t : ℝ => |t| * Real.exp ((‖z₀‖ + 1) * |t|))).continuousOn
    case h_diff =>
      apply Filter.Eventually.of_forall
      intro t _ht x _hx
      show HasDerivAt (fun z => Complex.exp (-z * ↑t) * f t)
        (-(↑t : ℂ) * Complex.exp (-x * ↑t) * f t) x
      have h1 : HasDerivAt (fun z => -z * (↑t : ℂ)) (-(↑t : ℂ)) x := by
        simpa using (hasDerivAt_neg x).mul_const (↑t : ℂ)
      convert (HasDerivAt.cexp h1).mul_const (f t) using 1; ring
  ·
    have heq : truncatedLaplaceTransform f T = fun _ => 0 := by
      ext z; unfold truncatedLaplaceTransform
      apply intervalIntegral.integral_undef
      intro h; apply hf
      have h2 := h.continuousOn_mul
        (by fun_prop : Continuous (fun t : ℝ => Complex.exp (z * ↑t))).continuousOn
      convert h2 using 1; ext t
      have key : Complex.exp (-z * ↑t) * Complex.exp (z * ↑t) = 1 := by
        rw [← Complex.exp_add]; simp [neg_mul, neg_add_cancel]
      calc f t = 1 * f t := (one_mul _).symm
        _ = (Complex.exp (-z * ↑t) * Complex.exp (z * ↑t)) * f t := by rw [key]
        _ = Complex.exp (z * ↑t) * (Complex.exp (-z * ↑t) * f t) := by ring
    rw [heq]; exact differentiable_const 0

theorem newman_cif_H_diffOn_closedBall
    (f : ℝ → ℂ) (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (Tv : ℝ)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z) :
    DifferentiableOn ℂ
      (fun z => Complex.exp (z * ↑Tv) * (1 + z ^ 2 / (↑R : ℂ) ^ 2) *
        (g z - truncatedLaplaceTransform f Tv z))
      (Metric.closedBall 0 ↑R) := by
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall 0 ↑R) :=
    newman_g_diffOn_closedBall g R hR hg_diffAt

  have hgT : DifferentiableOn ℂ (truncatedLaplaceTransform f Tv) (Metric.closedBall 0 ↑R) :=
    (truncatedLaplaceTransform_differentiable f Tv).differentiableOn
  have hR_ne : (↑R : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hR)
  have hexp : DifferentiableOn ℂ (fun z => Complex.exp (z * ↑Tv)) (Metric.closedBall 0 ↑R) :=
    fun z _ => ((differentiableAt_id.mul (differentiableAt_const _)).cexp).differentiableWithinAt
  have hpoly : DifferentiableOn ℂ (fun z => 1 + z ^ 2 / (↑R : ℂ) ^ 2) (Metric.closedBall 0 ↑R) :=
    fun z _ => ((differentiableAt_const _).add
      ((differentiableAt_id.pow 2).div (differentiableAt_const _)
        (pow_ne_zero _ hR_ne))).differentiableWithinAt
  exact (hexp.mul hpoly).mul (hg_ball.sub hgT)

theorem newman_cif_equation6
    (f : ℝ → ℂ) (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z) (Tv : ℝ)
    (w : ℝ → ℂ) (hw : w = fun (θ : ℝ) => (↑R : ℂ) * Complex.exp ((↑θ : ℂ) * I))
    (integrand : ℝ → ℝ → ℂ)
    (hintegrand : integrand = fun (T : ℝ) (θ : ℝ) =>
      (2 * ↑Real.pi * I)⁻¹ *
      (Complex.exp (w θ * ↑T) * (1 + (w θ)^2 / ↑(R^2 : ℝ)) / (w θ)) *
      (I * w θ)) :
    g 0 - truncatedLaplaceTransform f Tv 0 =
      ∫ θ in (-Real.pi/2)..(3*Real.pi/2),
        integrand Tv θ * (g (w θ) - truncatedLaplaceTransform f Tv (w θ)) := by
  set H : ℂ → ℂ := fun z => Complex.exp (z * ↑Tv) * (1 + z ^ 2 / (↑R : ℂ) ^ 2) *
    (g z - truncatedLaplaceTransform f Tv z) with hH_def
  have h2pi_ne : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero _ (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    exact_mod_cast (two_ne_zero : (2 : ℝ) ≠ 0)
  have hR_ne : (↑R : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hR)

  have hcif : ∮ z in C(0, ↑R), (z - 0)⁻¹ • H z = (2 * ↑Real.pi * I) • H 0 :=
    DifferentiableOn.circleIntegral_sub_inv_smul
      (newman_cif_H_diffOn_closedBall f g R hR Tv hg_diffAt)
      (by simp [Metric.mem_ball]; exact_mod_cast hR)
  simp only [smul_eq_mul, sub_zero] at hcif

  have h0 : H 0 = g 0 - truncatedLaplaceTransform f Tv 0 := by
    show Complex.exp (0 * ↑Tv) * (1 + 0 ^ 2 / (↑R : ℂ) ^ 2) *
      (g 0 - truncatedLaplaceTransform f Tv 0) = g 0 - truncatedLaplaceTransform f Tv 0
    simp [zero_mul, exp_zero, zero_pow, zero_div, add_zero]
  rw [h0] at hcif

  have hcirc : ∮ z in C(0, ↑R), z⁻¹ * H z =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), I * H (↑R * Complex.exp (↑θ * I)) := by
    simp only [circleIntegral, smul_eq_mul]; congr 1; ext θ
    rw [deriv_circleMap, circleMap_zero]
    have : (↑R : ℂ) * Complex.exp ((↑θ : ℂ) * I) ≠ 0 :=
      mul_ne_zero hR_ne (exp_ne_zero _)
    field_simp

  calc g 0 - truncatedLaplaceTransform f Tv 0
      = (2 * ↑Real.pi * I)⁻¹ * (2 * ↑Real.pi * I *
          (g 0 - truncatedLaplaceTransform f Tv 0)) := by
            rw [inv_mul_cancel_left₀ h2pi_ne]
    _ = (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(0, ↑R), z⁻¹ * H z := by rw [hcif]
    _ = (2 * ↑Real.pi * I)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), I * H (↑R * Complex.exp (↑θ * I)) := by
            rw [hcirc]
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (2 * ↑Real.pi * I)⁻¹ * (I * H (↑R * Complex.exp (↑θ * I))) := by
            exact (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ θ in (-Real.pi / 2)..(3 * Real.pi / 2),
          (2 * ↑Real.pi * I)⁻¹ * (I * H (↑R * Complex.exp (↑θ * I))) := by

            have hper : Function.Periodic
                (fun θ : ℝ => (2 * ↑Real.pi * I)⁻¹ *
                  (I * H (↑R * Complex.exp (↑θ * I)))) (2 * Real.pi) := by
              intro θ
              show (2 * ↑Real.pi * I)⁻¹ * (I * H (↑R * Complex.exp (↑(θ + 2 * Real.pi) * I))) =
                   (2 * ↑Real.pi * I)⁻¹ * (I * H (↑R * Complex.exp (↑θ * I)))
              congr 1; congr 1
              simp only [ofReal_add, add_mul, exp_add]
              rw [show Complex.exp (↑(2 * Real.pi) * I) = 1 from by
                rw [ofReal_mul, ofReal_ofNat]; exact exp_two_pi_mul_I, mul_one]
            have h_eq := hper.intervalIntegral_add_eq 0 (-(Real.pi / 2))
            simp only [zero_add] at h_eq; rw [h_eq]; congr 1 <;> linarith
    _ = ∫ θ in (-Real.pi / 2)..(3 * Real.pi / 2),
          integrand Tv θ * (g (w θ) - truncatedLaplaceTransform f Tv (w θ)) := by

            congr 1; ext θ
            rw [hintegrand, hw]; simp only
            set wv := (↑R : ℂ) * Complex.exp ((↑θ : ℂ) * I)
            have hwv_ne : wv ≠ 0 := mul_ne_zero hR_ne (exp_ne_zero _)
            have hR_cast : (↑(R ^ 2 : ℝ) : ℂ) = (↑R : ℂ) ^ 2 := by push_cast; ring
            show (2 * ↑Real.pi * I)⁻¹ * (I * (Complex.exp (wv * ↑Tv) *
              (1 + wv ^ 2 / (↑R : ℂ) ^ 2) *
              (g wv - truncatedLaplaceTransform f Tv wv))) = _
            rw [show (1 + wv ^ 2 / ↑(R ^ 2 : ℝ)) = (1 + wv ^ 2 / (↑R : ℂ) ^ 2)
              from by rw [hR_cast]]
            field_simp

theorem newman_integrand_intervalIntegrable
    (phi : ℝ → ℂ) (hphi : Continuous phi) (R T a b : ℝ)
    (w : ℝ → ℂ) (hw : w = fun (θ : ℝ) => (↑R : ℂ) * Complex.exp ((↑θ : ℂ) * I))
    (integrand : ℝ → ℝ → ℂ)
    (hintegrand : integrand = fun (S : ℝ) (θ : ℝ) =>
      (2 * ↑Real.pi * I)⁻¹ *
      (Complex.exp (w θ * ↑S) * (1 + (w θ)^2 / ↑(R^2 : ℝ)) / (w θ)) *
      (I * w θ)) :
    IntervalIntegrable (fun θ => integrand T θ * phi θ) volume a b := by
  by_cases hR : R = 0
  ·
    have : (fun θ => integrand T θ * phi θ) = fun _ => 0 := by
      ext θ; subst hintegrand; subst hw; simp [hR]
    rw [this]; exact continuous_const.intervalIntegrable a b
  ·
    apply Continuous.intervalIntegrable
    subst hw; subst hintegrand
    fun_prop (disch := intro θ; exact mul_ne_zero (by exact_mod_cast hR) (Complex.exp_ne_zero _))

theorem newman_g_continuous_on_circle
    (g : ℂ → ℂ) (R : ℝ) (_hR : 0 < R)
    (hg_cont : Continuous g) :
    Continuous (fun θ : ℝ => g (↑R * Complex.exp (↑θ * I))) := by
  apply hg_cont.comp
  exact continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))

theorem newman_cauchy_identity
    (f : ℝ → ℂ) (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z)
    (hg_cont : Continuous g) :
    let w : ℝ → ℂ := fun θ => ↑R * Complex.exp (↑θ * I)
    let integrand : ℝ → ℝ → ℂ := fun T θ =>
      (2 * ↑Real.pi * I)⁻¹ *
      (Complex.exp (w θ * ↑T) * (1 + (w θ)^2 / ↑(R^2 : ℝ)) / (w θ)) *
      (I * w θ)
    let I_plus : ℝ → ℂ := fun T =>
      ∫ θ in (-Real.pi/2)..(Real.pi/2),
        integrand T θ * (g (w θ) - truncatedLaplaceTransform f T (w θ))
    let I_minus_gT : ℝ → ℂ := fun T =>
      ∫ θ in (Real.pi/2)..(3*Real.pi/2),
        integrand T θ * (-truncatedLaplaceTransform f T (w θ))
    let I_minus_g : ℝ → ℂ := fun T =>
      g 0 - truncatedLaplaceTransform f T 0 - I_plus T - I_minus_gT T
    ∀ T, I_minus_g T = ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), integrand T θ * g (w θ) := by
  intro w integrand I_plus I_minus_gT I_minus_g Tv

  have hgw_cont := newman_g_continuous_on_circle g R hR hg_cont
  have hgTw_cont : Continuous (fun θ => truncatedLaplaceTransform f Tv (w θ)) :=
    (truncatedLaplaceTransform_continuous f Tv).comp (by fun_prop)

  have h_cif := newman_cif_equation6 f g R hR hg_diffAt Tv w rfl integrand rfl

  show g 0 - truncatedLaplaceTransform f Tv 0 - I_plus Tv - I_minus_gT Tv = _
  rw [h_cif]

  have hiR := newman_integrand_intervalIntegrable
    (fun θ => g (w θ) - truncatedLaplaceTransform f Tv (w θ))
    (hgw_cont.sub hgTw_cont)
    R Tv (-Real.pi/2) (Real.pi/2) w rfl integrand rfl
  have hiL := newman_integrand_intervalIntegrable
    (fun θ => g (w θ) - truncatedLaplaceTransform f Tv (w θ))
    (hgw_cont.sub hgTw_cont)
    R Tv (Real.pi/2) (3*Real.pi/2) w rfl integrand rfl

  change (∫ θ in (-Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * (g (w θ) - truncatedLaplaceTransform f Tv (w θ))) -
    (∫ θ in (-Real.pi/2)..(Real.pi/2),
      integrand Tv θ * (g (w θ) - truncatedLaplaceTransform f Tv (w θ))) -
    (∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * (-truncatedLaplaceTransform f Tv (w θ))) = _
  rw [(intervalIntegral.integral_add_adjacent_intervals hiR hiL).symm]

  have hig := newman_integrand_intervalIntegrable
    (fun θ => g (w θ)) hgw_cont R Tv (Real.pi/2) (3*Real.pi/2) w rfl integrand rfl
  have higt := newman_integrand_intervalIntegrable
    (fun θ => truncatedLaplaceTransform f Tv (w θ))
    hgTw_cont R Tv (Real.pi/2) (3*Real.pi/2) w rfl integrand rfl

  have hpw_sub : (fun θ => integrand Tv θ *
      (g (w θ) - truncatedLaplaceTransform f Tv (w θ))) =
    (fun θ => integrand Tv θ * g (w θ) -
      integrand Tv θ * truncatedLaplaceTransform f Tv (w θ)) := by
    ext θ; ring
  have hpw_neg : (fun θ => integrand Tv θ *
      (-truncatedLaplaceTransform f Tv (w θ))) =
    (fun θ => -(integrand Tv θ * truncatedLaplaceTransform f Tv (w θ))) := by
    ext θ; ring

  have hsplit : ∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * (g (w θ) - truncatedLaplaceTransform f Tv (w θ)) =
    (∫ θ in (Real.pi/2)..(3*Real.pi/2), integrand Tv θ * g (w θ)) -
    ∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * truncatedLaplaceTransform f Tv (w θ) := by
    rw [hpw_sub]; exact intervalIntegral.integral_sub hig higt

  have hneg : ∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * (-truncatedLaplaceTransform f Tv (w θ)) =
    -(∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand Tv θ * truncatedLaplaceTransform f Tv (w θ)) := by
    rw [hpw_neg]; exact intervalIntegral.integral_neg

  simp only [hsplit, hneg]
  ring

lemma one_add_exp_two_mul_I (θ : ℝ) :
    (1 : ℂ) + Complex.exp (2 * ↑θ * I) = 2 * ↑(Real.cos θ) * Complex.exp (↑θ * I) := by
  rw [show 2 * ↑θ * I = ↑θ * I + ↑θ * I from by ring, Complex.exp_add, Complex.exp_mul_I]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · simp [Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
    ring

lemma norm_one_add_exp_two_mul_I (θ : ℝ) :
    ‖(1 : ℂ) + Complex.exp (2 * ↑θ * I)‖ = 2 * |Real.cos θ| := by
  rw [one_add_exp_two_mul_I, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]

lemma w_sq_div_R_sq (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    let w : ℂ := ↑R * Complex.exp (↑θ * I)
    w ^ 2 / ↑(R ^ 2 : ℝ) = Complex.exp (2 * ↑θ * I) := by
  simp only
  rw [mul_pow, show (↑R : ℂ) ^ 2 * Complex.exp (↑θ * I) ^ 2 / ↑(R ^ 2 : ℝ) =
    ((↑R : ℂ) ^ 2 / ↑(R ^ 2 : ℝ)) * Complex.exp (↑θ * I) ^ 2 from by ring]
  have : (↑R : ℂ) ^ 2 / ↑(R ^ 2 : ℝ) = 1 := by
    push_cast; exact div_self (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hR.ne'))
  rw [this, one_mul, ← Complex.exp_nat_mul]; push_cast; ring_nf

lemma exp_mul_truncLaplace_norm_le (f : ℝ → ℂ) (B : ℝ) (hB : 0 < B)
    (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (hT : 0 < T) (s : ℂ) (hs : s.re < 0) :
    ‖Complex.exp (s * ↑T)‖ * ‖truncatedLaplaceTransform f T s‖ ≤ B / (-s.re) := by
  unfold truncatedLaplaceTransform
  set a := -s.re with ha_def
  have ha : 0 < a := neg_pos.mpr hs
  have ha_ne : a ≠ 0 := ne_of_gt ha

  have h_bound_gT : ‖∫ t in (0 : ℝ)..T, Complex.exp (-s * ↑t) * f t‖ ≤
      ∫ t in (0 : ℝ)..T, Real.exp (a * t) * B := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT.le
    · apply Filter.Eventually.of_forall
      intro t ht
      rw [norm_mul, Complex.norm_exp]
      have hre_eq : (-s * ↑t).re = a * t := by
        simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, ha_def]
      rw [hre_eq]
      gcongr
      exact hf t (le_of_lt ht.1)
    · exact (Continuous.intervalIntegrable (by fun_prop) 0 T)

  have h_int : ∫ t in (0 : ℝ)..T, Real.exp (a * t) * B = B * (Real.exp (a * T) - 1) / a := by
    rw [show (fun t => Real.exp (a * t) * B) = (fun t => B * Real.exp (a * t)) from by ext; ring]
    rw [intervalIntegral.integral_const_mul]
    have h1 : ∫ t in (0 : ℝ)..T, Real.exp (a * t) =
        a⁻¹ * (Real.exp (a * T) - Real.exp (a * 0)) := by
      have : ∫ t in (0 : ℝ)..T, Real.exp (a * t) =
          a⁻¹ • ∫ u in (a * 0)..(a * T), Real.exp u := by
        rw [← intervalIntegral.integral_comp_mul_left _ ha_ne]
      rw [this, integral_exp, smul_eq_mul]
    rw [h1]; simp only [mul_zero, Real.exp_zero]; ring

  calc ‖Complex.exp (s * ↑T)‖ * ‖∫ t in (0 : ℝ)..T, Complex.exp (-s * ↑t) * f t‖
      ≤ ‖Complex.exp (s * ↑T)‖ * (∫ t in (0 : ℝ)..T, Real.exp (a * t) * B) := by gcongr
    _ = Real.exp (-a * T) * (∫ t in (0 : ℝ)..T, Real.exp (a * t) * B) := by
        rw [Complex.norm_exp]
        congr 1
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          ha_def, neg_neg]
    _ = Real.exp (-a * T) * (B * (Real.exp (a * T) - 1) / a) := by rw [h_int]
    _ ≤ B / a := by
        rw [show Real.exp (-a * T) * (B * (Real.exp (a * T) - 1) / a) =
          B * (Real.exp (-a * T) * (Real.exp (a * T) - 1)) / a from by ring]
        rw [mul_sub, ← Real.exp_add, show -a * T + a * T = 0 from by ring,
          Real.exp_zero, mul_one]
        rw [show B * (1 - Real.exp (-a * T)) / a =
          B / a * (1 - Real.exp (-a * T)) from by ring]
        calc B / a * (1 - Real.exp (-a * T))
            ≤ B / a * 1 := by
              gcongr
              linarith [Real.exp_pos (-a * T)]
          _ = B / a := mul_one _

set_option maxHeartbeats 800000 in
lemma exp_mul_laplace_tail_norm_le (f : ℝ → ℂ) (B : ℝ) (hB : 0 < B)
    (hf_bound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hf_loc : LocallyIntegrableOn f (Ici 0) volume)
    (g : ℂ → ℂ)
    (hg_eq : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), Complex.exp (-z * ↑t) * f t)
    (T : ℝ) (hT : 0 < T) (w : ℂ) (hw : 0 < w.re) :
    ‖Complex.exp (w * ↑T) * (g w - truncatedLaplaceTransform f T w)‖ ≤ B / w.re := by
  set h := fun t : ℝ => Complex.exp (-w * ↑t) * f t with hh_def
  have hw_re_neg : -w.re < 0 := by linarith

  have hh_int : IntegrableOn h (Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (by linarith : -w.re < 0) 0).const_mul B).mono
    · apply AEStronglyMeasurable.mul
      · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
      · exact (hf_loc.aestronglyMeasurable).mono_set Ioi_subset_Ici_self
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hre : (-w * ↑t).re = -w.re * t := by
        simp [mul_re, neg_re, ofReal_re, ofReal_im]
      rw [hre]
      calc Real.exp (-w.re * t) * ‖f t‖
          ≤ Real.exp (-w.re * t) * B := by
            gcongr; exact hf_bound t (le_of_lt (mem_Ioi.mp ht))
        _ = B * Real.exp (-w.re * t) := by ring

  have hg_val : g w = ∫ t in Ioi (0:ℝ), h t := hg_eq w hw

  have hdelta_eq : g w - truncatedLaplaceTransform f T w = ∫ t in Ioi T, h t := by
    rw [hg_val]
    unfold truncatedLaplaceTransform
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hh_int (le_of_lt hT)
    rw [← hsplit]; ring
  rw [hdelta_eq]

  have htail : ‖∫ t in Ioi T, h t‖ ≤ B * Real.exp (-w.re * T) / w.re := by
    calc ‖∫ t in Ioi T, h t‖
        ≤ ∫ t in Ioi T, B * Real.exp (-w.re * t) := by
          apply norm_integral_le_of_norm_le
            ((integrableOn_exp_mul_Ioi hw_re_neg T).const_mul B)
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [norm_mul, Complex.norm_exp]
          have hre : (-w * ↑t).re = -w.re * t := by
            simp [mul_re, neg_re, ofReal_re, ofReal_im]
          rw [hre]
          calc Real.exp (-w.re * t) * ‖f t‖
              ≤ Real.exp (-w.re * t) * B := by
                gcongr; exact hf_bound t (le_of_lt (by linarith [mem_Ioi.mp ht]))
            _ = B * Real.exp (-w.re * t) := by ring
      _ = B * Real.exp (-w.re * T) / w.re := by
          rw [integral_const_mul, integral_exp_mul_Ioi hw_re_neg T]; field_simp

  rw [norm_mul, Complex.norm_exp]
  have hre_wT : (w * ↑T).re = w.re * T := by simp [mul_re, ofReal_re, ofReal_im]
  rw [hre_wT]
  calc Real.exp (w.re * T) * ‖∫ t in Ioi T, h t‖
      ≤ Real.exp (w.re * T) * (B * Real.exp (-w.re * T) / w.re) := by gcongr
    _ = B / w.re := by
        rw [show Real.exp (w.re * T) * (B * Real.exp (-w.re * T) / w.re)
            = B / w.re * (Real.exp (w.re * T) * Real.exp (-w.re * T)) from by ring]
        rw [← Real.exp_add, show w.re * T + (-w.re * T) = 0 from by ring,
          Real.exp_zero, mul_one]

set_option maxHeartbeats 800000 in
lemma newman_iplus_pointwise_bound
    (f : ℝ → ℂ) (B : ℝ) (hB_pos : 0 < B)
    (hf_bound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hf_loc : LocallyIntegrableOn f (Ici 0) volume)
    (g : ℂ → ℂ)
    (hg_eq : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Ioi (0 : ℝ), Complex.exp (-z * ↑t) * f t)
    (R : ℝ) (hR : 0 < R) (T : ℝ) (hT : 0 < T) (θ : ℝ)
    (hθ : θ ∈ Set.uIoc (-Real.pi / 2) (Real.pi / 2)) :
    let wθ := (↑R : ℂ) * Complex.exp (↑θ * I)
    ‖((2 : ℂ) * ↑Real.pi * I)⁻¹ *
      (Complex.exp (wθ * ↑T) * (1 + wθ ^ 2 / ↑(R ^ 2 : ℝ)) / wθ) *
      (I * wθ) * (g wθ - truncatedLaplaceTransform f T wθ)‖ ≤ B / (Real.pi * R) := by
  simp only
  set wθ := (↑R : ℂ) * Complex.exp (↑θ * I) with hwθ_def
  set delta := g wθ - truncatedLaplaceTransform f T wθ with hdelta_def
  have hwθ_ne : wθ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
  have hR_ne : (↑R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hR2_ne : (↑(R ^ 2 : ℝ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero 2 hR_ne

  have integrand_eq : ((2 : ℂ) * ↑Real.pi * Complex.I)⁻¹ *
      (Complex.exp (wθ * ↑T) * (1 + wθ ^ 2 / ↑(R ^ 2 : ℝ)) / wθ) *
      (Complex.I * wθ) * delta =
    ((2 : ℂ) * ↑Real.pi)⁻¹ * ((Complex.exp (wθ * ↑T) * delta) *
      (1 + wθ ^ 2 / ↑(R ^ 2 : ℝ))) := by
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero, hwθ_ne, hR2_ne, hR_ne]
  rw [integrand_eq, norm_mul, norm_mul,
    w_sq_div_R_sq R hR θ, norm_one_add_exp_two_mul_I θ,
    norm_inv, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

  have hab : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [Set.uIoc_of_le hab] at hθ
  have hθ_ub : θ ≤ Real.pi / 2 := hθ.2
  have hcos_ge : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ_ub⟩
  by_cases hcos_zero : Real.cos θ = 0
  ·
    rw [hcos_zero, abs_zero, mul_zero, mul_zero, mul_zero]
    positivity
  ·
    have hcos_pos : 0 < Real.cos θ := lt_of_le_of_ne hcos_ge (Ne.symm hcos_zero)
    have hre : wθ.re = R * Real.cos θ := by
      simp [hwθ_def, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re,
            Complex.exp_ofReal_mul_I_im, Complex.ofReal_im]
    have hre_pos : 0 < wθ.re := by rw [hre]; positivity

    have h_prod_bound : ‖Complex.exp (wθ * ↑T) * delta‖ ≤ B / (R * Real.cos θ) := by
      have := exp_mul_laplace_tail_norm_le f B hB_pos hf_bound hf_loc g hg_eq T hT wθ hre_pos
      rwa [hre] at this

    calc (2 * Real.pi)⁻¹ * (‖Complex.exp (wθ * ↑T) * delta‖ * (2 * |Real.cos θ|))
        ≤ (2 * Real.pi)⁻¹ * (B / (R * Real.cos θ) * (2 * |Real.cos θ|)) := by gcongr
      _ = B / (Real.pi * R) := by
          rw [abs_of_pos hcos_pos]
          field_simp [Real.pi_ne_zero, ne_of_gt hR, ne_of_gt hcos_pos]

theorem newman_contour_decomposition
    (f : ℝ → ℂ) (B : ℝ) (hB_pos : 0 < B)
    (hf_bound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hf_loc : LocallyIntegrableOn f (Ici 0) volume)
    (g : ℂ → ℂ)
    (hg_eq : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Ioi (0 : ℝ), Complex.exp (-z * ↑t) * f t)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z)
    (hg_cont : Continuous g)
    (R : ℝ) (hR : 0 < R) :
    ∃ (I_plus I_minus_gT I_minus_g : ℝ → ℂ),

      (∀ T, 0 < T → g 0 - truncatedLaplaceTransform f T 0 =
        I_plus T + I_minus_gT T + I_minus_g T) ∧

      (∀ T, 0 < T → ‖I_plus T‖ ≤ B / R) ∧

      (∀ T, 0 < T → ‖I_minus_gT T‖ ≤ B / R) ∧

      (Tendsto I_minus_g atTop (𝓝 0)) := by

  let w : ℝ → ℂ := fun θ => ↑R * Complex.exp (↑θ * I)


  let integrand : ℝ → ℝ → ℂ := fun T θ =>
    (2 * ↑Real.pi * I)⁻¹ *
    (Complex.exp (w θ * ↑T) * (1 + (w θ)^2 / ↑(R^2 : ℝ)) / (w θ)) *
    (I * w θ)

  let I_plus : ℝ → ℂ := fun T =>
    ∫ θ in (-Real.pi/2)..(Real.pi/2),
      integrand T θ * (g (w θ) - truncatedLaplaceTransform f T (w θ))

  let I_minus_gT : ℝ → ℂ := fun T =>
    ∫ θ in (Real.pi/2)..(3*Real.pi/2),
      integrand T θ * (-truncatedLaplaceTransform f T (w θ))

  let I_minus_g : ℝ → ℂ := fun T =>
    g 0 - truncatedLaplaceTransform f T 0 - I_plus T - I_minus_gT T
  exact ⟨I_plus, I_minus_gT, I_minus_g,
    fun T _ => by simp only [I_minus_g]; ring,
    fun T hT => by
      show ‖∫ θ in (-Real.pi / 2)..(Real.pi / 2),
        integrand T θ * (g (w θ) - truncatedLaplaceTransform f T (w θ))‖ ≤ B / R
      calc ‖∫ θ in (-Real.pi / 2)..(Real.pi / 2),
              integrand T θ * (g (w θ) - truncatedLaplaceTransform f T (w θ))‖
          ≤ B / (Real.pi * R) * |Real.pi / 2 - (-Real.pi / 2)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
              simp only [integrand, w]
              exact newman_iplus_pointwise_bound f B hB_pos hf_bound hf_loc g hg_eq R hR T hT θ hθ
        _ = B / R := by
            rw [show Real.pi / 2 - (-Real.pi / 2) = Real.pi from by ring]
            rw [abs_of_pos Real.pi_pos]
            have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            field_simp,
    fun T hT => by
      show ‖∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
        integrand T θ * (-truncatedLaplaceTransform f T (w θ))‖ ≤ B / R
      calc ‖∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
              integrand T θ * (-truncatedLaplaceTransform f T (w θ))‖
          ≤ B / (Real.pi * R) * |3 * Real.pi / 2 - Real.pi / 2| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by

              simp only [integrand, w]
              set wθ := ↑R * Complex.exp (↑θ * Complex.I) with hwθ_def
              set gTθ := truncatedLaplaceTransform f T wθ
              have hwθ_ne : wθ ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
              have hR_ne : (↑R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
              have hR2_ne : (↑(R ^ 2 : ℝ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero 2 hR_ne

              have integrand_eq : ((2 : ℂ) * ↑Real.pi * Complex.I)⁻¹ *
                  (Complex.exp (wθ * ↑T) * (1 + wθ ^ 2 / ↑(R ^ 2 : ℝ)) / wθ) *
                  (Complex.I * wθ) * (-gTθ) =
                -(((2 : ℂ) * ↑Real.pi)⁻¹ * ((Complex.exp (wθ * ↑T) * gTθ) *
                  (1 + wθ ^ 2 / ↑(R ^ 2 : ℝ)))) := by
                field_simp [Real.pi_ne_zero, Complex.I_ne_zero, hwθ_ne, hR2_ne, hR_ne]
              rw [integrand_eq, norm_neg, norm_mul, norm_mul,
                w_sq_div_R_sq R hR θ, norm_one_add_exp_two_mul_I θ,
                norm_inv, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos Real.pi_pos]


              have hab : Real.pi / 2 ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
              rw [Set.uIoc_of_le hab] at hθ
              have hθ_lb : Real.pi / 2 ≤ θ := le_of_lt hθ.1
              have hcos_le : Real.cos θ ≤ 0 :=
                Real.cos_nonpos_of_pi_div_two_le_of_le hθ_lb (by linarith [hθ.2])
              rcases hcos_le.eq_or_lt with hcos_eq | hcos_neg
              ·
                rw [abs_eq_zero.mpr hcos_eq, mul_zero, mul_zero, mul_zero]
                positivity
              ·
                have hre : wθ.re = R * Real.cos θ := by simp [hwθ_def]
                have hre_neg : wθ.re < 0 := by rw [hre]; exact mul_neg_of_pos_of_neg hR hcos_neg
                have hneg_re : -wθ.re = R * |Real.cos θ| := by
                  rw [hre, abs_of_neg hcos_neg]; ring
                have h_prod_bound : ‖Complex.exp (wθ * ↑T) * gTθ‖ ≤ B / (R * |Real.cos θ|) := by
                  calc ‖Complex.exp (wθ * ↑T) * gTθ‖
                      ≤ ‖Complex.exp (wθ * ↑T)‖ * ‖gTθ‖ := norm_mul_le _ _
                    _ ≤ B / (-wθ.re) := exp_mul_truncLaplace_norm_le f B hB_pos hf_bound T hT wθ hre_neg
                    _ = B / (R * |Real.cos θ|) := by rw [hneg_re]
                calc (2 * Real.pi)⁻¹ * (‖Complex.exp (wθ * ↑T) * gTθ‖ * (2 * |Real.cos θ|))
                    ≤ (2 * Real.pi)⁻¹ * (B / (R * |Real.cos θ|) * (2 * |Real.cos θ|)) := by gcongr
                  _ = B / (Real.pi * R) := by
                      field_simp [Real.pi_ne_zero, ne_of_gt hR,
                        ne_of_gt (abs_pos.mpr (ne_of_lt hcos_neg))]

        _ = B / R := by
            rw [show 3 * Real.pi / 2 - Real.pi / 2 = Real.pi from by ring]
            rw [abs_of_pos Real.pi_pos]
            have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            field_simp,
    by


      suffices h_cauchy : ∃ (hfun : ℝ → ℂ),
          (∀ T, I_minus_g T = ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.exp (↑R * Complex.exp (↑θ * I) * ↑T) * hfun θ) ∧
          Integrable hfun (volume.restrict (Ioc (Real.pi / 2) (3 * Real.pi / 2))) ∧
          AEStronglyMeasurable hfun volume by
        obtain ⟨hfun, hfun_eq, hfun_int, hfun_meas⟩ := h_cauchy
        exact (left_semicircle_integral_tendsto R hR hfun hfun_int hfun_meas).congr
          (fun T => (hfun_eq T).symm)

      let hf : ℝ → ℂ := fun θ =>
        (2 * ↑Real.pi * I)⁻¹ * (1 + (↑R * cexp (↑θ * I))^2 / ↑(R^2 : ℝ)) * I *
          g (↑R * cexp (↑θ * I))
      have hgw_cont := newman_g_continuous_on_circle g R hR hg_cont
      have nhfun_cont : Continuous hf :=
        Continuous.mul (Continuous.mul (Continuous.mul continuous_const
          (by fun_prop)) continuous_const) hgw_cont
      have h_cif := newman_cauchy_identity f g R hR hg_diffAt hg_cont
      refine ⟨hf, ?_, ?_, ?_⟩
      · intro T
        rw [show I_minus_g T = ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2),
              integrand T θ * g (w θ) from h_cif T]
        congr 1; ext θ; simp only [hf, integrand, w]
        have hw_ne : (↑R : ℂ) * cexp (↑θ * I) ≠ 0 :=
          mul_ne_zero (by exact_mod_cast hR.ne') (Complex.exp_ne_zero _)
        have hR_ne : (↑R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        field_simp [hw_ne, hR_ne]
      · exact (nhfun_cont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self
      · exact nhfun_cont.aestronglyMeasurable⟩

lemma newman_combined_estimate
    (f : ℝ → ℂ) (B : ℝ) (hB_pos : 0 < B)
    (hf_bound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (hf_loc : LocallyIntegrableOn f (Ici 0) volume)
    (g : ℂ → ℂ)
    (hg_eq : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Ioi (0 : ℝ), Complex.exp (-z * ↑t) * f t)
    (hg_diffAt : ∀ z, DifferentiableAt ℂ g z)
    (hg_cont : Continuous g)
    (R : ℝ) (hR : 0 < R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ‖g 0 - ∫ t in (0 : ℝ)..T, f t‖ < 2 * B / R + ε := by

  obtain ⟨I_plus, I_minus_gT, I_minus_g, hdecomp, hplus_bound, hminus_bound, hvanish⟩ :=
    newman_contour_decomposition f B hB_pos hf_bound hf_loc g hg_eq hg_diffAt hg_cont R hR

  rw [NormedAddCommGroup.tendsto_atTop] at hvanish
  obtain ⟨N₁, hN₁⟩ := hvanish ε hε
  rw [eventually_atTop]
  refine ⟨max N₁ 1, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith [le_max_right N₁ 1, hT]
  have hTN₁ : N₁ ≤ T := le_trans (le_max_left N₁ 1) hT

  rw [← truncatedLaplaceTransform_zero f T, hdecomp T hTpos]

  have h3 : ‖I_minus_g T‖ < ε := by
    have := hN₁ T hTN₁; simp only [sub_zero] at this; exact this

  calc ‖I_plus T + I_minus_gT T + I_minus_g T‖
      ≤ ‖I_plus T‖ + ‖I_minus_gT T‖ + ‖I_minus_g T‖ := by
        linarith [norm_add_le (I_plus T + I_minus_gT T) (I_minus_g T),
                   norm_add_le (I_plus T) (I_minus_gT T)]
    _ < 2 * B / R + ε := by
        have : B / R + B / R = 2 * B / R := by ring
        linarith [hplus_bound T hTpos, hminus_bound T hTpos]

end



noncomputable section


end

end Newman

open Set Asymptotics

theorem zeta_sub_one_div_holomorphic_extension :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {s | 0 < s.re} ∧
      ∀ s, 0 < s.re → s ≠ 1 → f s = riemannZeta s - 1 / (s - 1) := by

  set g : ℂ → ℂ := fun s ↦ riemannZeta s - 1 / (s - 1) with hg_def

  refine ⟨Function.update g 1 (limUnder (𝓝[≠] 1) g), ?_, ?_⟩
  ·
    have h_nhds : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp [one_re])
    have h_diff : DifferentiableOn ℂ g ({s : ℂ | 0 < s.re} \ {1}) := by
      intro s hs
      have hs_ne : s ≠ 1 := fun h => hs.2 (mem_singleton_iff.mpr h)
      exact ((differentiableAt_riemannZeta hs_ne).sub
        ((differentiableAt_const 1).div (differentiableAt_id.sub (differentiableAt_const 1))
          (sub_ne_zero.mpr hs_ne))).differentiableWithinAt


    have h_littleO : (fun z => g z - g 1) =o[𝓝[≠] 1] fun z => (z - 1)⁻¹ :=
      (tendsto_riemannZeta_sub_one_div.sub tendsto_const_nhds).norm.isBoundedUnder_le
        |>.isLittleO_sub_self_inv
    exact Complex.differentiableOn_update_limUnder_of_isLittleO h_nhds h_diff h_littleO
  ·
    intro s _ hs_ne
    exact Function.update_of_ne hs_ne ..

open Asymptotics Finset

open scoped ArithmeticFunction Chebyshev

theorem chebyshevTheta_isBigO :
    (fun x : ℝ => θ x) =O[atTop] id := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4, ?_⟩
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.norm_of_nonneg (Chebyshev.theta_nonneg x), id, Real.norm_of_nonneg hx]
  exact Chebyshev.theta_le_log4_mul_x hx

theorem phi_sub_pole_holomorphic_extension :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | 1 ≤ s.re} ∧
      ∀ s, 1 ≤ s.re → s ≠ 1 →
        F s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) := by

  obtain ⟨f, hf_diff, hf_eq⟩ := zeta_sub_one_div_holomorphic_extension


  set Ψ : ℂ → ℂ := fun s => (s - 1) * f s + 1 with hΨ_def

  have hΨ_eq : ∀ s, 0 < s.re → s ≠ 1 → Ψ s = (s - 1) * riemannZeta s := by
    intro s hs hs_ne
    simp only [hΨ_def, hf_eq s hs hs_ne]
    have : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne
    field_simp; ring

  have hΨ_diff : DifferentiableOn ℂ Ψ {s | 0 < s.re} :=
    ((differentiableOn_id.sub (differentiableOn_const 1)).mul hf_diff).add
      (differentiableOn_const 1)

  have hU_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re

  have h_sub : {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 0 < s.re} := fun s hs => by
    simp only [Set.mem_setOf_eq] at *; linarith

  have hΨ_ne : ∀ s, s ∈ ({s : ℂ | 1 ≤ s.re}) → Ψ s ≠ 0 := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_cases hs_ne : s = 1
    · subst hs_ne; simp [hΨ_def]
    · rw [hΨ_eq s (by linarith) hs_ne]
      exact mul_ne_zero (sub_ne_zero.mpr hs_ne) (riemannZeta_ne_zero_of_one_le_re hs)

  have hΨ_deriv_diff : DifferentiableOn ℂ (deriv Ψ) {s | 0 < s.re} :=
    hΨ_diff.deriv hU_open

  refine ⟨fun s => -(deriv Ψ s / Ψ s), ?_, ?_⟩
  ·
    exact (hΨ_deriv_diff.mono h_sub).div (hΨ_diff.mono h_sub) hΨ_ne |>.neg
  ·
    intro s hs hs_ne
    have hs_re' : 0 < s.re := by linarith

    have hΨ_eq_near : Ψ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
      have hU : {z : ℂ | 0 < z.re} ∩ {z | z ≠ 1} ∈ 𝓝 s :=
        Filter.inter_mem
          (hU_open.mem_nhds hs_re')
          (isOpen_ne.mem_nhds hs_ne)
      filter_upwards [hU] with z ⟨hz_re, hz_ne⟩
      show (z - 1) * f z + 1 = (z - 1) * riemannZeta z
      rw [hf_eq z hz_re hz_ne]
      have : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
      field_simp; ring

    have h_deriv_eq : deriv Ψ s = deriv (fun z => (z - 1) * riemannZeta z) s :=
      hΨ_eq_near.deriv_eq

    have h_prod_deriv : deriv (fun z => (z - 1) * riemannZeta z) s =
        riemannZeta s + (s - 1) * deriv riemannZeta s := by
      have hd := ((hasDerivAt_id s).sub_const 1).mul
        (differentiableAt_riemannZeta hs_ne).hasDerivAt
      simp only [one_mul] at hd
      exact hd.deriv

    have hΨ_val : Ψ s = (s - 1) * riemannZeta s :=
      hΨ_eq s hs_re' hs_ne


    show -(deriv Ψ s / Ψ s) = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)
    rw [h_deriv_eq, h_prod_deriv, hΨ_val]
    have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne
    have h2 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    field_simp
    ring
