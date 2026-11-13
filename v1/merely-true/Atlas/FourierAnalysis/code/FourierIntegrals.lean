/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory Filter Topology
open scoped Convolution ENNReal NNReal

noncomputable section

namespace ApproxIdentityR

def rescaledKernel (K : ℝ → ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  (1 / ε) * K (x / ε)



end ApproxIdentityR


namespace CesaroSummation

open ApproxIdentityR Real

def fejerKernelBase (x : ℝ) : ℝ :=
  if x = 0 then (2 * Real.pi)⁻¹
  else 2 * Real.sin (x / 2) ^ 2 / (Real.pi * x ^ 2)

def fejerKernel (N : ℝ) (x : ℝ) : ℝ :=
  N * fejerKernelBase (N * x)

lemma fejerKernelBase_nonneg (x : ℝ) : 0 ≤ fejerKernelBase x := by
  simp only [fejerKernelBase]; split_ifs <;> positivity

lemma sin_sq_half_le (x : ℝ) :
    Real.sin (x / 2) ^ 2 * (1 + x ^ 2) ≤ 2 * x ^ 2 := by
  have h1 : Real.sin (x / 2) ^ 2 ≤ 1 := sin_sq_le_one (x / 2)
  have h2 : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := @sin_sq_le_sq (x / 2)
  by_cases hx : x ^ 2 ≤ 4
  · nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  · push Not at hx; nlinarith

lemma fejerKernelBase_le_bound (x : ℝ) :
    fejerKernelBase x ≤ 4 / Real.pi * (1 + x ^ 2)⁻¹ := by
  simp only [fejerKernelBase]
  split_ifs with h
  · subst h
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, inv_one, mul_one]
    rw [show (2 * Real.pi)⁻¹ = 1 / (2 * Real.pi) from by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  · rw [div_le_iff₀ (by positivity : 0 < Real.pi * x ^ 2)]
    rw [show 4 / Real.pi * (1 + x ^ 2)⁻¹ * (Real.pi * x ^ 2) =
        4 * x ^ 2 / (1 + x ^ 2) from by field_simp]
    rw [le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
    nlinarith [sin_sq_half_le x]

lemma fejerKernelBase_measurable : Measurable fejerKernelBase := by
  unfold fejerKernelBase
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · apply Measurable.div <;> measurability

lemma fejerKernelBase_integrable : Integrable fejerKernelBase volume := by
  apply Integrable.mono ((integrable_inv_one_add_sq).const_mul (4 / Real.pi))
  · exact fejerKernelBase_measurable.aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    rw [norm_of_nonneg (fejerKernelBase_nonneg x)]
    simp only [norm_mul]
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 4 / Real.pi)]
    rw [norm_of_nonneg (by positivity : (0:ℝ) ≤ (1 + x ^ 2)⁻¹)]
    exact fejerKernelBase_le_bound x

open scoped intervalIntegral

lemma hasDerivAt_antideriv_cexp (a : ℂ) (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ((1 - (x : ℂ)) * Complex.exp (a * x) / a +
      Complex.exp (a * x) / a ^ 2))
    ((1 - (t : ℂ)) * Complex.exp (a * t)) t := by
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (a * (x : ℂ)))
      (Complex.exp (a * t) * a) t := by
    have h2 := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a
    rw [show a * Complex.ofRealCLM 1 = a from by simp] at h2
    exact h2.cexp
  have hsub : HasDerivAt (fun x : ℝ => (1 : ℂ) - (x : ℂ)) (-1 : ℂ) t := by
    simpa using (hasDerivAt_const t (1 : ℂ)).sub Complex.ofRealCLM.hasDerivAt
  refine ((hsub.mul hexp).div_const a |>.add (hexp.div_const _)).congr_deriv ?_
  field_simp; ring

lemma integral_one_sub_mul_cexp (a : ℂ) (ha : a ≠ 0) :
    ∫ ξ in (0:ℝ)..1, ((1 - (ξ : ℂ)) * Complex.exp (a * ξ)) =
    (Complex.exp a - 1 - a) / a ^ 2 := by
  have hint : IntervalIntegrable (fun ξ : ℝ => (1 - (ξ : ℂ)) * Complex.exp (a * ξ))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.sub Complex.continuous_ofReal.continuousOn).mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).continuousOn)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_antideriv_cexp a ha x) hint]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, sub_zero, mul_one]
  field_simp; ring

lemma integral_tri_cexp (a : ℂ) (ha : a ≠ 0) :
    ∫ ξ in (-1:ℝ)..1, ((1 - |(ξ : ℝ)|) : ℝ) * Complex.exp (a * ξ) =
    (Complex.exp a + Complex.exp (-a) - 2) / a ^ 2 := by
  have hcont : Continuous (fun ξ : ℝ => ((1 - |ξ|) : ℝ) * Complex.exp (a * ξ)) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub continuous_abs)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hII1 := hcont.continuousOn.intervalIntegrable
    (a := (-1:ℝ)) (b := (0:ℝ)) (μ := volume)
  have hII2 := hcont.continuousOn.intervalIntegrable
    (a := (0:ℝ)) (b := (1:ℝ)) (μ := volume)
  rw [← intervalIntegral.integral_add_adjacent_intervals hII1 hII2]
  have hpos : ∫ ξ in (0:ℝ)..1, ((1 - |ξ|) : ℝ) * Complex.exp (a * ξ) =
      ∫ ξ in (0:ℝ)..1, ((1 - (ξ : ℂ)) * Complex.exp (a * ξ)) := by
    apply intervalIntegral.integral_congr; intro ξ hξ
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hξ
    simp only [abs_of_nonneg hξ.1, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hpos, integral_one_sub_mul_cexp a ha]
  have ha' : -a ≠ 0 := neg_ne_zero.mpr ha
  suffices hneg : ∫ ξ in (-1:ℝ)..0, ((1 - |ξ|) : ℝ) * Complex.exp (a * ξ) =
      (Complex.exp (-a) - 1 - (-a)) / (-a) ^ 2 by
    rw [hneg, show (-a) ^ 2 = a ^ 2 from by ring]; field_simp; ring
  have h_eq : ∫ ξ in (-1:ℝ)..0, ((1 - |ξ|) : ℝ) * Complex.exp (a * ξ) =
      ∫ ξ in (-1:ℝ)..0, ((1 + ξ) : ℝ) * Complex.exp (a * ξ) := by
    apply intervalIntegral.integral_congr; intro ξ hξ
    simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hξ
    simp only [abs_of_nonpos hξ.2]; push_cast; ring
  rw [h_eq]
  let g : ℝ → ℂ := fun u => ((1 - u : ℝ) : ℂ) * Complex.exp ((-a) * u)
  have h_rw : ∀ ξ : ℝ, ((1 + ξ : ℝ) : ℂ) * Complex.exp (a * ξ) = g (-ξ) := by
    intro ξ; simp only [g]; push_cast; congr 1 <;> ring
  simp_rw [h_rw]
  rw [intervalIntegral.integral_comp_neg g (a := (-1:ℝ)) (b := 0)]
  simp only [neg_neg, neg_zero, g]
  have : ∀ u : ℝ, ((1 - u : ℝ) : ℂ) * Complex.exp ((-a) * u) =
      (1 - (u : ℂ)) * Complex.exp ((-a) * u) := by
    intro u; push_cast; ring
  simp_rw [this]
  exact integral_one_sub_mul_cexp (-a) ha'

theorem fourier_tri_ae_eq (w : ℝ) :
    ∫ ξ in (-1:ℝ)..1, ((1 - |(ξ : ℝ)|) : ℝ) *
      Complex.exp ((-2 * ↑π * Complex.I * ↑w) * ξ) =
    ↑(2 * π * fejerKernelBase (2 * π * w)) := by
  by_cases hw : w = 0
  · subst hw
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [fejerKernelBase, if_pos rfl]
    rw [show 2 * π * (2 * π)⁻¹ = (1 : ℝ) from
      mul_inv_cancel₀ (by positivity : (2 : ℝ) * π ≠ 0)]

    rw [intervalIntegral.integral_ofReal]
    congr 1


    have hII := intervalIntegral.integral_add_adjacent_intervals
      (show IntervalIntegrable (fun x => 1 - |x|) volume (-1:ℝ) 0 from by
        apply ContinuousOn.intervalIntegrable; fun_prop)
      (show IntervalIntegrable (fun x => 1 - |x|) volume (0:ℝ) 1 from by
        apply ContinuousOn.intervalIntegrable; fun_prop)
    rw [← hII]
    have h1 : ∫ x in (-1:ℝ)..0, (1 - |x|) = ∫ x in (-1:ℝ)..0, (1 + x) := by
      apply intervalIntegral.integral_congr; intro x hx
      simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0), Set.mem_Icc] at hx
      show 1 - |x| = 1 + x; rw [abs_of_nonpos hx.2]; ring
    have h2 : ∫ x in (0:ℝ)..1, (1 - |x|) = ∫ x in (0:ℝ)..1, (1 - x) := by
      apply intervalIntegral.integral_congr; intro x hx
      simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
      show 1 - |x| = 1 - x; rw [abs_of_nonneg hx.1]
    rw [h1, h2]


    have i1 : ∫ x in (-1:ℝ)..0, (1 + x) = 1/2 := by
      rw [show (fun x : ℝ => 1 + x) = fun x => 1 + id x from by ext; simp]
      rw [show (∫ x in (-1:ℝ)..0, (1 : ℝ) + id x) =
          (∫ x in (-1:ℝ)..0, (1 : ℝ)) + ∫ x in (-1:ℝ)..0, id x from
        intervalIntegral.integral_add
          intervalIntegral.intervalIntegrable_const
          (ContinuousOn.intervalIntegrable continuous_id.continuousOn)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, id]
      rw [integral_id]; ring
    have i2 : ∫ x in (0:ℝ)..1, (1 - x) = 1/2 := by
      rw [show (fun x : ℝ => 1 - x) = fun x => 1 - id x from by ext; simp]
      rw [show (∫ x in (0:ℝ)..1, (1 : ℝ) - id x) =
          (∫ x in (0:ℝ)..1, (1 : ℝ)) - ∫ x in (0:ℝ)..1, id x from
        intervalIntegral.integral_sub
          intervalIntegral.intervalIntegrable_const
          (ContinuousOn.intervalIntegrable continuous_id.continuousOn)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, id]
      rw [integral_id]; ring
    rw [i1, i2]; ring
  ·
    have ha : (-2 * (↑π : ℂ) * Complex.I * (↑w : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (two_ne_zero' ℂ)
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact Complex.ofReal_ne_zero.mpr hw
    rw [integral_tri_cexp _ ha]
    rw [show fejerKernelBase (2 * π * w) =
        2 * Real.sin (π * w) ^ 2 / (π * (2 * π * w) ^ 2) from by
      rw [fejerKernelBase, if_neg (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hw)]
      ring_nf]
    have hexp_sum : Complex.exp ((-2 * ↑π * Complex.I * ↑w)) +
        Complex.exp (-((-2 * ↑π * Complex.I * ↑w))) =
        2 * ↑(Real.cos (2 * π * w)) := by
      rw [show (-2 * (↑π : ℂ) * Complex.I * (↑w : ℂ)) =
          -(Complex.I * ↑(2 * π * w)) from by push_cast; ring]
      rw [neg_neg]
      rw [show Complex.exp (-(Complex.I * ↑(2 * π * w))) +
          Complex.exp (Complex.I * ↑(2 * π * w)) =
          2 * Complex.cos ↑(2 * π * w) from by rw [Complex.cos]; ring]
      rw [Complex.ofReal_cos]
    rw [hexp_sum]
    have hsq : ((-2 * (↑π : ℂ) * Complex.I * (↑w : ℂ))) ^ 2 =
        -(4 * (↑π : ℂ) ^ 2 * (↑w : ℂ) ^ 2) := by
      rw [show (-2 * (↑π : ℂ) * Complex.I * (↑w : ℂ)) ^ 2 =
          4 * (↑π : ℂ) ^ 2 * Complex.I ^ 2 * (↑w : ℂ) ^ 2 from by ring,
        Complex.I_sq]; ring
    rw [hsq]
    have hcos := Real.cos_two_mul_eq_one_sub (π * w)
    rw [show 2 * (π * w) = 2 * π * w from by ring] at hcos
    rw [show (2 : ℂ) * ↑(Real.cos (2 * π * w)) - 2 =
        ↑(2 * Real.cos (2 * π * w) - 2) from by push_cast; ring]
    rw [show (2:ℝ) * Real.cos (2 * π * w) - 2 = -(4 * Real.sin (π * w) ^ 2) from by linarith]
    have hpi : (↑π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hw' : (↑w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
    push_cast
    field_simp

open FourierTransform MeasureTheory Complex in
theorem fejerKernelBase_integral : ∫ x, fejerKernelBase x = 1 := by

  let tri : ℝ → ℂ := fun ξ => ↑(max (1 - |ξ|) 0 : ℝ)
  have htri_cont : Continuous tri :=
    Complex.continuous_ofReal.comp
      (Continuous.max (continuous_const.sub continuous_abs) continuous_const)
  have htri_int : Integrable tri volume := by
    exact htri_cont.integrable_of_hasCompactSupport (by
      rw [hasCompactSupport_def]
      apply IsCompact.closure_of_subset (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
      intro x hx
      simp only [tri, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hx
      have h2 : 0 < 1 - |x| := by
        by_contra h; push Not at h; exact hx (max_eq_right h)
      exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩)

  have hft : ∀ w, 𝓕 tri w = ↑(2 * π * fejerKernelBase (2 * π * w)) := by
    intro w
    show VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) tri w = _
    simp only [VectorFourier.fourierIntegral]
    have hsup : Function.support (fun v => (𝐞 (-((innerₗ ℝ) v) w)) • tri v) ⊆
        Set.Ioc (-1 : ℝ) 1 := by
      intro v hv
      simp only [Function.mem_support, ne_eq] at hv
      have htv : tri v ≠ 0 := fun h => hv (by rw [h, smul_zero])
      simp only [tri, ne_eq, Complex.ofReal_eq_zero] at htv
      have h2 : 0 < 1 - |v| := by
        by_contra h; push Not at h; exact htv (max_eq_right h)
      exact ⟨by linarith [neg_abs_le v], by linarith [le_abs_self v]⟩
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hsup]
    rw [intervalIntegral.integral_congr (fun v hv => ?_)]
    · exact fourier_tri_ae_eq w
    · simp only [tri, innerₗ_apply_apply]
      rw [show inner ℝ v w = v * w from by simp [inner, mul_comm]]
      rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, mul_comm]
      have hmax : (max (1 - |v|) 0 : ℝ) = 1 - |v| := by
        rw [max_eq_left]
        simp only [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1), Set.mem_Icc] at hv
        linarith [abs_le.mpr ⟨by linarith [hv.1], hv.2⟩]
      rw [show (↑(max (1 - |v|) 0 : ℝ) : ℂ) = ↑(1 - |v|) from by rw [hmax]]
      congr 1; congr 1; push_cast; ring

  have hft_int : Integrable (𝓕 tri) volume := by
    rw [show 𝓕 tri = fun w => (↑(2 * π * fejerKernelBase (2 * π * w)) : ℂ) from
      by ext w; exact hft w]
    exact (((integrable_comp_mul_left_iff fejerKernelBase
      (by positivity : (2:ℝ) * π ≠ 0)).mpr fejerKernelBase_integrable).const_mul _).ofReal

  have hinv := htri_int.fourierInv_fourier_eq hft_int htri_cont.continuousAt (v := (0 : ℝ))
  have h_inv_zero : 𝓕⁻ (𝓕 tri) (0 : ℝ) = ∫ w, 𝓕 tri w := by
    change VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) (𝓕 tri) 0 = _
    simp [VectorFourier.fourierIntegral]
  have htri_zero : tri 0 = (1 : ℂ) := by simp [tri]

  have hint_ft : ∫ w, 𝓕 tri w = (1 : ℂ) := by rw [← h_inv_zero, hinv, htri_zero]

  simp_rw [hft] at hint_ft
  have hfi : Integrable (fun w => (↑(2 * π * fejerKernelBase (2 * π * w)) : ℂ)) volume :=
    (((integrable_comp_mul_left_iff fejerKernelBase
      (by positivity : (2:ℝ) * π ≠ 0)).mpr fejerKernelBase_integrable).const_mul _).ofReal
  have h1 : (∫ w, (↑(2 * π * fejerKernelBase (2 * π * w)) : ℂ)).re =
      ∫ w, (↑(2 * π * fejerKernelBase (2 * π * w)) : ℂ).re :=
    (ContinuousLinearMap.integral_comp_comm Complex.reCLM hfi).symm
  rw [hint_ft, Complex.one_re] at h1
  simp only [Complex.ofReal_re] at h1
  rw [integral_const_mul, Measure.integral_comp_mul_left fejerKernelBase (2 * π)] at h1
  rw [abs_of_pos (inv_pos.mpr (by positivity : (2 : ℝ) * π > 0)), smul_eq_mul] at h1
  field_simp at h1
  linarith

lemma tendsto_inv_atTop_nhdsWithin_Ioi :
    Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact tendsto_inv_atTop_zero
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with N hN
    exact inv_pos.mpr (Set.mem_Ioi.mp hN)


end CesaroSummation

open scoped FourierTransform SchwartzMap
open Real MeasureTheory Complex

namespace SchwartzFourierInversion

def bookFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(I * ↑x * ↑ξ)) • f x

def bookFourierInv (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 : ℂ) / (2 * ↑π)) • ∫ ξ : ℝ, Complex.exp (I * ↑x * ↑ξ) • g ξ

theorem fourier_inversion (f : 𝓢(ℝ, ℂ)) :
    (𝓕⁻ (𝓕 f) : 𝓢(ℝ, ℂ)) = f :=
  FourierTransform.fourierInv_fourier_eq (E := 𝓢(ℝ, ℂ)) (F := 𝓢(ℝ, ℂ)) f

theorem fourierInv_eq_fourier_neg (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕⁻ f : 𝓢(ℝ, ℂ)) x = (𝓕 f : 𝓢(ℝ, ℂ)) (-x) := by
  rw [show (𝓕⁻ f : 𝓢(ℝ, ℂ)) x = ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x from rfl,
    SchwartzMap.fourierInv_coe f, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe f]

lemma real_inner_eq_mul (v w : ℝ) : @inner ℝ ℝ _ v w = v * w := by
  rw [show v = v • (1 : ℝ) from (smul_eq_mul v 1).symm ▸ (mul_one v).symm,
    real_inner_smul_left, real_inner_comm,
    show w = w • (1 : ℝ) from (smul_eq_mul w 1).symm ▸ (mul_one w).symm,
    real_inner_smul_left, @inner_self_eq_norm_sq_to_K ℝ ℝ]
  simp

lemma fourierChar_inner_eq_exp (v ξ : ℝ) :
    (𝐞 (-@inner ℝ ℝ _ v (ξ / (2 * π))) : ℂ) = Complex.exp (-(I * ↑v * ↑ξ)) := by
  rw [fourierChar_apply, real_inner_eq_mul]
  congr 1
  push_cast
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp

theorem bookFourier_eq_fourier_rescale (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    bookFourier (⇑f) ξ = (𝓕 f : 𝓢(ℝ, ℂ)) (ξ / (2 * π)) := by
  rw [show (𝓕 f : 𝓢(ℝ, ℂ)) (ξ / (2 * π)) =
      ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (ξ / (2 * π)) from rfl,
    SchwartzMap.fourier_coe f, fourier_eq]
  simp only [bookFourier]
  congr 1
  ext v
  congr 1
  rw [← fourierChar_inner_eq_exp]

theorem plancherel_schwartz_book (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ, ‖bookFourier (⇑f) ξ‖ ^ 2 = 2 * π * ∫ x, ‖f x‖ ^ 2 := by

  have h1 : ∀ ξ, ‖bookFourier (⇑f) ξ‖ ^ 2 = ‖(𝓕 f : 𝓢(ℝ, ℂ)) (ξ / (2 * π))‖ ^ 2 := by
    intro ξ
    rw [bookFourier_eq_fourier_rescale]
  simp_rw [h1]

  rw [Measure.integral_comp_div (fun η => ‖(𝓕 f : 𝓢(ℝ, ℂ)) η‖ ^ 2) (2 * π)]

  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_pos hpi, smul_eq_mul]

  rw [SchwartzMap.integral_norm_sq_fourier f]

end SchwartzFourierInversion

open scoped FourierTransform SchwartzMap
open FourierTransform

namespace TempDistFourierInversion

theorem fourier_fourierInv_tempered (T : 𝓢'(ℝ, ℂ)) :
    𝓕 (𝓕⁻ T) = T :=
  fourier_fourierInv_eq T

theorem fourierInv_fourier_tempered (T : 𝓢'(ℝ, ℂ)) :
    𝓕⁻ (𝓕 T) = T :=
  fourierInv_fourier_eq T

end TempDistFourierInversion

open scoped FourierTransform SchwartzMap ENNReal Topology
open MeasureTheory FourierTransform Filter

namespace L2FourierExtension

theorem fourier_schwartz_approx_tendsto
    (f : Lp (α := ℝ) ℂ 2 volume)
    (fj : ℕ → 𝓢(ℝ, ℂ))
    (hfj : Tendsto (fun j => (fj j).toLp 2 volume) atTop (𝓝 f)) :
    Tendsto (fun j => 𝓕 ((fj j).toLp 2 volume)) atTop (𝓝 (𝓕 f)) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.continuousAt.tendsto.comp hfj

theorem fourier_L2_linear_isometry_equiv :
    ∃ (e : (Lp (α := ℝ) ℂ 2 volume) ≃ₗᵢ[ℂ] (Lp (α := ℝ) ℂ 2 volume)),
    (∀ f, e f = 𝓕 f) ∧ (∀ f, e.symm f = 𝓕⁻ f) :=
  ⟨Lp.fourierTransformₗᵢ ℝ ℂ, fun _ => rfl, fun _ => rfl⟩

theorem plancherel_L2 (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖𝓕 f‖ = ‖f‖ :=
  Lp.norm_fourier_eq f

theorem fourier_inversion_L2' (f : Lp (α := ℝ) ℂ 2 volume) :
    𝓕 (𝓕⁻ f) = f :=
  FourierTransform.fourier_fourierInv_eq f

theorem fourier_L2_injective (f : Lp (α := ℝ) ℂ 2 volume)
    (hf : 𝓕 f = 0) : f = 0 := by
  have h1 : ‖𝓕 f‖ = ‖f‖ := plancherel_L2 f
  rw [hf, norm_zero] at h1
  exact norm_eq_zero.mp h1.symm

theorem fourier_L2_injective' :
    Function.Injective (𝓕 : Lp (α := ℝ) ℂ 2 volume → Lp (α := ℝ) ℂ 2 volume) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).injective

end L2FourierExtension

open scoped FourierTransform SchwartzMap ENNReal Topology
open MeasureTheory FourierTransform Filter Real Complex

namespace FourierInversionL2

def bookInverseFourier (f : ℝ → ℂ) (x : ℝ) : ℂ := 𝓕⁻ f x

theorem fourier_isometry_L2 (f : Lp (α := ℝ) ℂ 2 volume) :
    ‖𝓕 f‖ = ‖f‖ :=
  Lp.norm_fourier_eq f

theorem fourier_L2_equiv :
    ∃ (e : (Lp (α := ℝ) ℂ 2 volume) ≃ₗᵢ[ℂ] (Lp (α := ℝ) ℂ 2 volume)),
    (∀ f, e f = 𝓕 f) ∧ (∀ f, e.symm f = 𝓕⁻ f) ∧
    (∀ f, ‖e f‖ = ‖f‖) :=
  ⟨Lp.fourierTransformₗᵢ ℝ ℂ, fun _ => rfl, fun _ => rfl,
   fun f => Lp.norm_fourier_eq f⟩

end FourierInversionL2

open scoped FourierTransform SchwartzMap ENNReal Topology
open MeasureTheory FourierTransform Filter Real Complex

namespace InverseFourierL1L2Agreement

lemma neg_innerₗ_flip :
    ((-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)).flip = -innerₗ ℝ := by
  ext; simp [LinearMap.flip_apply]

theorem inverseFourier_L2_agrees_L1
    (h : ℝ → ℂ)
    (hh₁ : Integrable h volume)
    (hh₂ : MemLp h 2 volume) :
    (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) =ᵐ[volume] (𝓕⁻ h : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume)).locallyIntegrable one_le_two
  · exact (VectorFourier.fourierIntegral_continuous (W := ℝ) Real.continuous_fourierChar
      continuous_inner.neg hh₁).locallyIntegrable
  · intro g hg_smooth hg_supp
    have hg_C_cs : HasCompactSupport (Complex.ofReal ∘ g) :=
      hg_supp.comp_left Complex.ofReal_zero
    have hg_C_smooth : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofReal ∘ g) :=
      Complex.ofRealCLM.contDiff.comp hg_smooth
    let φ : SchwartzMap ℝ ℂ := hg_C_cs.toSchwartzMap hg_C_smooth
    have hφ_eq : ∀ x, (φ : ℝ → ℂ) x = (g x : ℂ) :=
      HasCompactSupport.toSchwartzMap_toFun hg_C_cs hg_C_smooth
    have td_lhs : ∫ ξ, φ ξ • (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) ξ =
        ∫ x, (𝓕⁻ φ x) • h x := by
      rw [(Lp.toTemperedDistribution_apply _ φ).symm,
          ← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
          Lp.toTemperedDistribution_apply]
      exact integral_congr_ae (by filter_upwards [hh₂.coeFn_toLp] with x hx; rw [hx])
    have parseval : ∫ ξ, (𝓕⁻ h ξ) • (φ ξ) = ∫ x, h x • (𝓕⁻ (φ : ℝ → ℂ) x) := by
      have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ ℝ) (W := ℝ)
        Real.continuous_fourierChar continuous_inner.neg hh₁ (φ.integrable (μ := volume))
      simp only [neg_innerₗ_flip] at key
      exact key
    have key_lhs : ∫ x, g x • (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) x =
        ∫ x, (𝓕⁻ (φ : SchwartzMap ℝ ℂ) x) • h x := by
      have : (fun x => g x • (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) x) =
             (fun x => φ x • (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) x) :=
        funext fun x => by rw [Complex.real_smul, hφ_eq, smul_eq_mul]
      rw [this]; exact td_lhs
    have key_rhs : ∫ x, g x • 𝓕⁻ h x =
        ∫ x, (𝓕⁻ (φ : SchwartzMap ℝ ℂ) x) • h x := by
      have step1 : (fun x => g x • 𝓕⁻ h x) = (fun x => (𝓕⁻ h x) • (φ x)) :=
        funext fun x => by
          rw [Complex.real_smul, smul_eq_mul, mul_comm, ← hφ_eq]
      rw [step1, parseval]
      congr 1; ext x; rw [SchwartzMap.fourierInv_coe, smul_eq_mul, smul_eq_mul, mul_comm]
    exact key_lhs.trans key_rhs.symm

theorem inverseFourier_L2_agrees_L1_book
    (h : ℝ → ℂ)
    (hh₁ : Integrable h volume)
    (hh₂ : MemLp h 2 volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      (𝓕⁻ (hh₂.toLp h) : Lp (α := ℝ) ℂ 2 volume) x =
      FourierInversionL2.bookInverseFourier h x :=
  inverseFourier_L2_agrees_L1 h hh₁ hh₂

end InverseFourierL1L2Agreement


open MeasureTheory Filter Topology Complex
open scoped FourierTransform SchwartzMap

namespace FourierInjectiveL1

open SchwartzFourierInversion (bookFourier)

def cesaroMean (f : ℝ → ℂ) (N : ℝ) (x : ℝ) : ℂ :=
  ((1 : ℂ) / (2 * ↑Real.pi)) •
    ∫ ξ : ℝ, Set.indicator (Set.Icc (-N) N)
      (fun ξ => ((1 : ℂ) - ↑|ξ| / ↑N) * (exp (I * ↑x * ↑ξ) * bookFourier f ξ)) ξ

lemma mathlib_fourier_eq_zero_of_bookFourier_eq_zero (f : ℝ → ℂ)
    (hhat : ∀ ξ, bookFourier f ξ = 0) :
    ∀ w : ℝ, FourierTransform.fourier f w = 0 := by
  intro w
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∫ v : ℝ, exp (↑(-2 * Real.pi * v * w) * I) • f v =
         bookFourier f (2 * Real.pi * w) := by
    simp only [SchwartzFourierInversion.bookFourier]
    congr 1
    ext v
    congr 1
    push_cast
    ring
  rw [this, hhat]

set_option maxHeartbeats 800000 in
theorem integral_smul_eq_zero_of_bookFourier_eq_zero
    (f : ℝ → ℂ) (hf : Integrable f volume)
    (hhat : ∀ ξ, bookFourier f ξ = 0)
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg_cs : HasCompactSupport g) :
    ∫ x : ℝ, g x • f x = 0 := by

  have hhat_mathlib : ∀ w : ℝ, FourierTransform.fourier f w = 0 :=
    mathlib_fourier_eq_zero_of_bookFourier_eq_zero f hhat

  have hg_C_cs : HasCompactSupport (Complex.ofReal ∘ g) :=
    hg_cs.comp_left Complex.ofReal_zero
  have hg_C_smooth : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofReal ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let φ : SchwartzMap ℝ ℂ := hg_C_cs.toSchwartzMap hg_C_smooth

  let ψ : SchwartzMap ℝ ℂ := 𝓕⁻ φ
  have hFψ : (𝓕 ψ : SchwartzMap ℝ ℂ) = φ := FourierTransform.fourier_fourierInv_eq φ
  have hFψ_fun : ∀ x, FourierTransform.fourier (ψ : ℝ → ℂ) x = (g x : ℂ) := by
    intro x
    have := congr_fun (SchwartzMap.fourier_coe ψ).symm x
    rw [this]; change (𝓕 ψ : SchwartzMap ℝ ℂ) x = _; rw [hFψ]
    exact HasCompactSupport.toSchwartzMap_toFun hg_C_cs hg_C_smooth x

  have hψ_int : Integrable (ψ : ℝ → ℂ) volume := ψ.integrable
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by ext; simp
  have parseval := VectorFourier.integral_fourierIntegral_smul_eq_flip (V := ℝ) (W := ℝ)
    (f := f) (g := (ψ : ℝ → ℂ)) (μ := volume) (ν := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hψ_int
  rw [hflip] at parseval

  have lhs_zero : ∫ ξ : ℝ,
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f ξ) • (ψ : ℝ → ℂ) ξ = 0 := by
    simp_rw [show ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f ξ =
      FourierTransform.fourier f ξ from fun _ => rfl, hhat_mathlib, zero_smul]
    exact integral_zero ℝ ℂ
  rw [lhs_zero] at parseval

  simp_rw [show ∀ x, f x • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (ψ : ℝ → ℂ) x =
    f x • (g x : ℂ) from fun x => by congr 1; exact hFψ_fun x] at parseval

  simp_rw [show ∀ x, g x • f x = f x • (g x : ℂ) from
    fun x => by simp [real_smul, smul_eq_mul, mul_comm]]
  exact parseval.symm

theorem fourier_injective_L1 (f : ℝ → ℂ) (hf : Integrable f volume)
    (hhat : ∀ ξ, bookFourier f ξ = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hg_cs
  exact integral_smul_eq_zero_of_bookFourier_eq_zero f hf hhat g (by exact hg) hg_cs

end FourierInjectiveL1

open scoped FourierTransform SchwartzMap ENNReal Topology
open MeasureTheory FourierTransform Filter

namespace L2L1FourierAgree

theorem fourier_L2_eq_L1
    (f : ℝ → ℂ) (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    ((𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] (𝓕 f : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume)).locallyIntegrable one_le_two
  · exact (VectorFourier.fourierIntegral_continuous (W := ℝ) Real.continuous_fourierChar
      continuous_inner (memLp_one_iff_integrable.mp hf1)).locallyIntegrable
  · intro g hg_smooth hg_supp
    have hf_int : Integrable f volume := memLp_one_iff_integrable.mp hf1
    have hg_C_cs : HasCompactSupport (Complex.ofReal ∘ g) := hg_supp.comp_left Complex.ofReal_zero
    have hg_C_smooth : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofReal ∘ g) :=
      Complex.ofRealCLM.contDiff.comp hg_smooth
    let φ : SchwartzMap ℝ ℂ := hg_C_cs.toSchwartzMap hg_C_smooth
    have hφ_eq : ∀ x, (φ : ℝ → ℂ) x = (g x : ℂ) :=
      HasCompactSupport.toSchwartzMap_toFun hg_C_cs hg_C_smooth
    have td_lhs : ∫ ξ, φ ξ • (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) ξ =
        ∫ x, (𝓕 φ x) • f x := by
      rw [(Lp.toTemperedDistribution_apply _ φ).symm,
          ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
          Lp.toTemperedDistribution_apply]
      exact integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    have parseval : ∫ ξ, (𝓕 f ξ) • (φ ξ) = ∫ x, f x • (𝓕 (φ : ℝ → ℂ) x) := by
      simpa using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (W := ℝ)
        Real.continuous_fourierChar continuous_inner hf_int φ.integrable
    have key_lhs : ∫ x, g x • (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x =
        ∫ x, (𝓕 (φ : SchwartzMap ℝ ℂ) x) • f x := by
      have : (fun x => g x • (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x) =
             (fun x => φ x • (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x) :=
        funext fun x => by rw [Complex.real_smul, hφ_eq, smul_eq_mul]
      rw [this]; exact td_lhs
    have key_rhs : ∫ x, g x • 𝓕 f x = ∫ x, (𝓕 (φ : SchwartzMap ℝ ℂ) x) • f x := by
      have step1 : (fun x => g x • 𝓕 f x) = (fun x => (𝓕 f x) • (φ x)) :=
        funext fun x => by
          rw [Complex.real_smul, smul_eq_mul, mul_comm, ← hφ_eq]
      rw [step1, parseval]
      congr 1; ext x; rw [SchwartzMap.fourier_coe, smul_eq_mul, smul_eq_mul, mul_comm]
    exact key_lhs.trans key_rhs.symm

end L2L1FourierAgree
