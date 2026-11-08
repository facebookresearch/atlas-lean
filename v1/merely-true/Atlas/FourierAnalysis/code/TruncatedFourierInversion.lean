/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology Set
open scoped FourierTransform ENNReal NNReal

noncomputable section

namespace TruncatedFourierInversion

lemma tendsto_eLpNorm_indicator_compl_Icc {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    Tendsto (fun N : ℕ => eLpNorm ((Icc (-(N : ℝ)) N)ᶜ.indicator g) 2 volume)
      atTop (𝓝 0) := by
  set g' := hg.1.mk g
  have hg'_sm : StronglyMeasurable g' := hg.1.stronglyMeasurable_mk
  have hg'_ae : g =ᶠ[ae volume] g' := hg.1.ae_eq_mk
  have hg'_lp : MemLp g' 2 volume := hg.ae_eq hg'_ae
  suffices h : Tendsto (fun N : ℕ => eLpNorm ((Icc (-(N : ℝ)) N)ᶜ.indicator g') 2 volume)
      atTop (𝓝 0) by
    exact h.congr (fun N => (eLpNorm_congr_ae hg'_ae.indicator).symm)
  suffices h_lint : Tendsto
    (fun N : ℕ => ∫⁻ x : ℝ, (‖(Icc (-(N : ℝ)) N)ᶜ.indicator g' x‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂volume)
    atTop (𝓝 0) by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [enorm_eq_nnnorm]
    rw [show (0 : ℝ≥0∞) = 0 ^ (1 / 2 : ℝ) from by simp]
    exact (ENNReal.continuous_rpow_const.tendsto 0).comp h_lint
  rw [show (0 : ℝ≥0∞) = ∫⁻ (_ : ℝ), (0 : ℝ≥0∞) ∂volume from by simp]
  apply tendsto_lintegral_of_dominated_convergence (fun x => (‖g' x‖₊ : ℝ≥0∞) ^ (2 : ℝ))
  · intro N
    exact (hg'_sm.indicator measurableSet_Icc.compl).measurable.nnnorm.coe_nnreal_ennreal.pow_const _
  · intro N
    apply Eventually.of_forall
    intro x
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 2)
    simp only [ENNReal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm]
    exact Set.indicator_le_self _ _ _
  · have h2 := hg'_lp.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h2
    simp only [ENNReal.toReal_ofNat] at h2
    simp_rw [enorm_eq_nnnorm] at h2
    intro h_eq; rw [h_eq] at h2; simp at h2
  · apply Eventually.of_forall
    intro x
    apply tendsto_atTop_of_eventually_const (i₀ := Nat.ceil |x|)
    intro N hN
    have hx_le : |x| ≤ N := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hN)
    have hx : x ∈ Icc (-(N : ℝ)) N := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have hx_compl : x ∉ (Icc (-(N : ℝ)) N)ᶜ := by rwa [Set.mem_compl_iff, not_not]
    simp only [Set.indicator_apply, if_neg hx_compl, nnnorm_zero, ENNReal.coe_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]

lemma truncated_fourier_hat_memLp (f : Lp (α := ℝ) ℂ 2 volume) (N : ℝ) :
    MemLp ((Icc (-N) N).indicator (𝓕 f : Lp (α := ℝ) ℂ 2 volume)) 2 volume :=
  (Lp.memLp (𝓕 f)).indicator measurableSet_Icc

theorem truncated_fourier_inversion_L2 (f : Lp (α := ℝ) ℂ 2 volume) :
    Tendsto (fun N : ℕ =>
      ‖f - 𝓕⁻ ((truncated_fourier_hat_memLp f N).toLp _)‖) atTop (𝓝 0) := by

  have h𝓕inv : (𝓕⁻ : Lp (α := ℝ) ℂ 2 volume → _) = (Lp.fourierTransformₗᵢ ℝ ℂ).symm := rfl

  have h_eq : ∀ N : ℕ,
      ‖f - 𝓕⁻ ((truncated_fourier_hat_memLp f N).toLp _)‖ =
      ‖𝓕 f - (truncated_fourier_hat_memLp f N).toLp _‖ := by
    intro N
    set a := (truncated_fourier_hat_memLp f N).toLp _

    calc ‖f - 𝓕⁻ a‖
        = ‖𝓕⁻ (𝓕 f) - 𝓕⁻ a‖ := by rw [FourierTransform.fourierInv_fourier_eq]
      _ = ‖𝓕⁻ (𝓕 f - a)‖ := by
          congr 1; rw [h𝓕inv]
          exact (map_sub (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearIsometry.toLinearMap
            (𝓕 f) a).symm
      _ = ‖𝓕 f - a‖ := by rw [h𝓕inv]; exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
  simp_rw [h_eq]

  have h_norm_eq : ∀ N : ℕ,
      ‖𝓕 f - (truncated_fourier_hat_memLp f N).toLp _‖ =
      (eLpNorm ((Icc (-(N : ℝ)) N)ᶜ.indicator
        (𝓕 f : Lp (α := ℝ) ℂ 2 volume)) 2 volume).toReal := by
    intro N
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (𝓕 f) ((truncated_fourier_hat_memLp f N).toLp _),
                     (truncated_fourier_hat_memLp f N).coeFn_toLp] with x hx1 hx2
    rw [hx1, Pi.sub_apply, hx2]
    simp only [Set.indicator_apply, mem_compl_iff]
    split_ifs <;> simp_all
  simp_rw [h_norm_eq]

  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_eLpNorm_indicator_compl_Icc (Lp.memLp (𝓕 f)))

end TruncatedFourierInversion
