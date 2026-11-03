/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory MeasureTheory.Measure AddCircle
open scoped ENNReal NNReal Convolution

noncomputable section

namespace TorusConvolution

variable {T : ℝ} [hT : Fact (0 < T)]

abbrev mulℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

set_option maxHeartbeats 800000 in
theorem eLpNorm_convolution_le
    {f g : AddCircle T → ℂ}
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) :
    eLpNorm (f ⋆[mulℂ, haarAddCircle] g) 1 haarAddCircle ≤
    eLpNorm f 1 haarAddCircle * eLpNorm g 1 haarAddCircle := by

  simp only [eLpNorm_one_eq_lintegral_enorm]
  show ∫⁻ x, ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ ∂haarAddCircle ≤ _


  calc ∫⁻ x, ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ ∂haarAddCircle

      ≤ ∫⁻ x, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        gcongr with x
        calc ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ
            = ‖∫ t, f t * g (x - t) ∂haarAddCircle‖ₑ := by rfl
          _ ≤ ∫⁻ t, ‖f t * g (x - t)‖ₑ ∂haarAddCircle :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle := by
              gcongr with t
              simp only [enorm_eq_nnnorm]
              exact_mod_cast nnnorm_mul_le (f t) (g (x - t))

    _ = ∫⁻ t, (∫⁻ x, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        rw [lintegral_lintegral_swap]

        exact ((hf.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
          quasiMeasurePreserving_snd).mul
          ((hg.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant haarAddCircle haarAddCircle))

    _ = ∫⁻ t, ‖f t‖ₑ * (∫⁻ x, ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        congr 1; ext t
        rw [lintegral_const_mul']
        simp [enorm_eq_nnnorm, ENNReal.coe_ne_top]

    _ = ∫⁻ t, ‖f t‖ₑ * (∫⁻ x, ‖g x‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        congr 1; ext t; congr 1
        exact lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t

    _ = (∫⁻ t, ‖f t‖ₑ ∂haarAddCircle) * (∫⁻ x, ‖g x‖ₑ ∂haarAddCircle) := by
        rw [lintegral_mul_const']
        simp_rw [enorm_eq_nnnorm]
        exact hg.2.ne

end TorusConvolution

end

open MeasureTheory Filter Topology Set intervalIntegral Real

noncomputable section

namespace ApproximateIdentity

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

lemma periodic_continuous_uniformContinuous {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hper : Function.Periodic f p) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hcomp : IsCompact (Icc (-p) (2 * p)) := isCompact_Icc
  have huc := hcomp.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc ε hε
  use min δ₀ (p / 2)
  refine ⟨lt_min hδ₀_pos (by linarith), ?_⟩
  intro a b hab
  set n₀ := ⌊a / p⌋
  have hfa : f a = f (a - n₀ • p) := (hper.sub_zsmul_eq n₀).symm
  have hfb : f b = f (b - n₀ • p) := (hper.sub_zsmul_eq n₀).symm
  rw [dist_eq_norm, hfa, hfb, ← dist_eq_norm]
  set a' := a - n₀ • p
  set b' := b - n₀ • p
  have ha'_lb : 0 ≤ a' := by
    simp only [a', zsmul_eq_mul]
    linarith [show (⌊a / p⌋ : ℝ) * p ≤ a from by rw [← le_div_iff₀ hp]; exact Int.floor_le _]
  have ha'_ub : a' < p := by
    simp only [a', zsmul_eq_mul]
    linarith [show a < ((⌊a / p⌋ : ℝ) + 1) * p from by
      rw [← div_lt_iff₀ hp]; exact Int.lt_floor_add_one _]
  have hdist_eq : dist a' b' = dist a b := by simp only [a', b', dist_sub_right]
  have hdist_small : dist a' b' < p / 2 := by
    rw [hdist_eq]; exact lt_of_lt_of_le hab (min_le_right _ _)
  have hab'_range := abs_lt.mp (by rwa [Real.dist_eq] at hdist_small)
  exact hδ₀ a' (by constructor <;> linarith) b'
    (by constructor <;> linarith [hab'_range.1, hab'_range.2])
    (by rw [hdist_eq]; exact lt_of_lt_of_le hab (min_le_left _ _))

lemma convolution_sub_eq (f K : ℝ → ℝ) (x : ℝ)
    (hK : IntervalIntegrable K volume (-π) π)
    (hfK : IntervalIntegrable (fun y => f (x - y) * K y) volume (-π) π)
    (hnorm : (1 / (2 * π)) * ∫ y in (-π)..π, K y = 1) :
    periodicConvolution f K x - f x =
      (1 / (2 * π)) * ∫ y in (-π)..π, (f (x - y) - f x) * K y := by
  unfold periodicConvolution
  have hint_K_val : ∫ y in (-π)..π, K y = 2 * π := by
    have : (1 : ℝ) / (2 * π) ≠ 0 := by positivity
    field_simp at hnorm; linarith
  have key : ∫ y in (-π)..π, (f (x - y) - f x) * K y =
      (∫ y in (-π)..π, f (x - y) * K y) - f x * (∫ y in (-π)..π, K y) := by
    rw [show (fun y => (f (x - y) - f x) * K y) = (fun y => f (x - y) * K y - f x * K y) from
      by ext y; ring, integral_sub hfK (hK.const_mul (f x)),
      intervalIntegral.integral_const_mul]
  rw [key, hint_K_val]; field_simp

lemma integral_subinterval_le_of_nonneg (g : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hg_intble : IntervalIntegrable g volume a d)
    (hg_nonneg : ∀ x ∈ Icc a d, 0 ≤ g x) :
    ∫ x in b..c, g x ≤ ∫ x in a..d, g x := by
  have had : a ≤ d := le_trans hab (le_trans hbc hcd)
  have hab_intble : IntervalIntegrable g volume a b :=
    hg_intble.mono_set (by rw [uIcc_of_le hab, uIcc_of_le had]; exact Icc_subset_Icc le_rfl (le_trans hbc hcd))
  have hbc_intble : IntervalIntegrable g volume b c :=
    hg_intble.mono_set (by rw [uIcc_of_le hbc, uIcc_of_le had]; exact Icc_subset_Icc hab hcd)
  have hcd_intble : IntervalIntegrable g volume c d :=
    hg_intble.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le had]; exact Icc_subset_Icc (le_trans hab hbc) le_rfl)
  have h3 := integral_add_adjacent_intervals (hab_intble.trans hbc_intble) hcd_intble
  have h1 := integral_add_adjacent_intervals hab_intble hbc_intble
  have hab_nn : 0 ≤ ∫ x in a..b, g x :=
    intervalIntegral.integral_nonneg hab (fun u hu => hg_nonneg u ⟨hu.1, le_trans hu.2 (le_trans hbc hcd)⟩)
  have hcd_nn : 0 ≤ ∫ x in c..d, g x :=
    intervalIntegral.integral_nonneg hcd (fun u hu => hg_nonneg u ⟨le_trans hab (le_trans hbc hu.1), hu.2⟩)
  linarith

theorem approximate_identity_lemma
    (f : ℝ → ℝ) (K : ℕ → ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f (2 * π))
    (hK_intble : ∀ N, IntervalIntegrable (K N) volume (-π) π)
    (hfK_intble : ∀ N x, IntervalIntegrable (fun y => f (x - y) * K N y) volume (-π) π)
    (habs_K_intble : ∀ N, IntervalIntegrable (fun y => |K N y|) volume (-π) π)
    (hdiff_K_intble : ∀ N x,
      IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π)
    (h_normalize : ∀ N, (1 / (2 * π)) * ∫ x in (-π)..π, K N x = 1)
    (h_bound : ∃ M : ℝ, ∀ N, ∫ x in (-π)..π, |K N x| ≤ M)
    (h_concentrate : ∀ δ, 0 < δ → δ ≤ π →
      Filter.Tendsto (fun N => (∫ x in (-π)..(-δ), |K N x|) + ∫ x in δ..π, |K N x|)
        Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |f x - periodicConvolution f (K N) x| ≤ ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := h_bound
  have hM_nonneg : 0 ≤ M := le_trans
    (intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun u _ => abs_nonneg _)) (hM 0)
  have hf_uc := periodic_continuous_uniformContinuous (by positivity : (0 : ℝ) < 2 * π)
    hf_cont hf_periodic
  have hf_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C := by
    have hne : (Icc (0 : ℝ) (2 * π)).Nonempty := nonempty_Icc.mpr (by positivity)
    obtain ⟨x₀, _, hx₀_max⟩ :=
      isCompact_Icc.exists_isMaxOn hne hf_cont.abs.continuousOn
    refine ⟨|f x₀|, abs_nonneg _, fun z => ?_⟩
    set n := ⌊z / (2 * π)⌋
    rw [show f z = f (z - n • (2 * π)) from (hf_periodic.sub_zsmul_eq n).symm]
    apply hx₀_max
    simp only [zsmul_eq_mul]
    have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
    have hlb : (⌊z / (2 * π)⌋ : ℝ) * (2 * π) ≤ z := by
      rw [← le_div_iff₀ h2pi_pos]; exact Int.floor_le _
    have hub : z < ((⌊z / (2 * π)⌋ : ℝ) + 1) * (2 * π) := by
      rw [← div_lt_iff₀ h2pi_pos]; exact Int.lt_floor_add_one _
    exact ⟨by linarith, by linarith⟩
  obtain ⟨C, hC_nonneg, hC⟩ := hf_bdd
  rw [Metric.uniformContinuous_iff] at hf_uc
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := hf_uc (ε * π / (M + 1)) (by positivity)
  set δ' := min (δ / 2) π with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min (by linarith) pi_pos
  have hδ'_le_π : δ' ≤ π := min_le_right _ _
  have hneg_π_le_neg_δ' : -π ≤ -δ' := by linarith
  have huc_bound : ∀ x y : ℝ, |y| ≤ δ' → |f (x - y) - f x| ≤ ε * π / (M + 1) := by
    intro x y hy
    exact le_of_lt (hδ_uc (by
      rw [dist_eq_norm, show (x - y) - x = -y from by ring, norm_neg, Real.norm_eq_abs]
      exact lt_of_le_of_lt hy (lt_of_le_of_lt (min_le_left _ _) (by linarith))))
  have h_conc_δ := h_concentrate δ' hδ'_pos hδ'_le_π
  rw [Metric.tendsto_atTop] at h_conc_δ
  obtain ⟨N₀, hN₀⟩ := h_conc_δ (ε * π / (2 * C + 1)) (by positivity)
  have htail : ∀ N ≥ N₀,
      (∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y| < ε * π / (2 * C + 1) := by
    intro N hN
    have h_dist := hN₀ N hN
    rw [Real.dist_eq, sub_zero] at h_dist
    rwa [abs_of_nonneg] at h_dist
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg hneg_π_le_neg_δ' (fun u _ => abs_nonneg _)
    · exact intervalIntegral.integral_nonneg hδ'_le_π (fun u _ => abs_nonneg _)
  use N₀
  intro N hN x
  have h_eq := convolution_sub_eq f (K N) x (hK_intble N) (hfK_intble N x) (h_normalize N)
  rw [abs_sub_comm]
  rw [h_eq]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hnorm_le := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hpi_le
    (f := fun y => (f (x - y) - f x) * K N y)
  simp only [Real.norm_eq_abs] at hnorm_le
  have habs_sub : IntervalIntegrable (fun y => |K N y|) volume (-π) π := habs_K_intble N
  have hdiff_sub : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π :=
    hdiff_K_intble N x
  have habs_sub_1 : IntervalIntegrable (fun y => |K N y|) volume (-π) (-δ') :=
    habs_sub.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
  have habs_sub_2 : IntervalIntegrable (fun y => |K N y|) volume (-δ') δ' :=
    habs_sub.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
  have habs_sub_3 : IntervalIntegrable (fun y => |K N y|) volume δ' π :=
    habs_sub.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hdiff_sub_1 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) (-δ') :=
    hdiff_sub.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
  have hdiff_sub_2 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-δ') δ' :=
    hdiff_sub.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
  have hdiff_sub_3 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume δ' π :=
    hdiff_sub.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
  have h_split : ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| =
      (∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
      + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
      + ∫ y in δ'..π, |(f (x - y) - f x) * K N y| := by
    have h_abs_eq : (fun y => |(f (x - y) - f x) * K N y|) = (fun y => |f (x - y) - f x| * |K N y|) :=
      by ext y; exact abs_mul _ _
    have h_abs_intble : IntervalIntegrable (fun y => |(f (x - y) - f x) * K N y|) volume (-π) π := by
      rw [h_abs_eq]; exact hdiff_K_intble N x
    have h_abs_intble_1 := h_abs_intble.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
    have h_abs_intble_2 := h_abs_intble.mono_set (by rw [uIcc_of_le (by linarith : -δ' ≤ δ'), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
    have h_abs_intble_3 := h_abs_intble.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
    have h12 := integral_add_adjacent_intervals h_abs_intble_1 h_abs_intble_2
    have h123 := integral_add_adjacent_intervals (h_abs_intble_1.trans h_abs_intble_2) h_abs_intble_3
    rw [← h123, ← h12]
  have h_near : ∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y| ≤
      ε * π / (M + 1) * ∫ y in (-δ')..δ', |K N y| := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on (by linarith) hdiff_sub_2 (habs_sub_2.const_mul _)
    intro y hy
    exact mul_le_mul_of_nonneg_right
      (huc_bound x y (by rw [abs_le]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩))
      (abs_nonneg _)
  have h_near_K_le : ∫ y in (-δ')..δ', |K N y| ≤ M :=
    le_trans (integral_subinterval_le_of_nonneg _ _ _ _ _
      hneg_π_le_neg_δ' (by linarith) hδ'_le_π (habs_K_intble N)
      (fun y _ => abs_nonneg _)) (hM N)
  have h_far1 : ∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in (-π)..(-δ'), |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hneg_π_le_neg_δ' hdiff_sub_1 (habs_sub_1.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have h_far2 : ∫ y in δ'..π, |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in δ'..π, |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hδ'_le_π hdiff_sub_3 (habs_sub_3.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have htail_N := htail N hN
  have htail_bound : 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|) ≤
      2 * C * (ε * π / (2 * C + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt htail_N) (by positivity)
  calc 1 / (2 * π) * |∫ y in (-π)..π, (f (x - y) - f x) * K N y|
      _ ≤ 1 / (2 * π) * ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| := by
          exact mul_le_mul_of_nonneg_left hnorm_le (by positivity)
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
          + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
          + ∫ y in δ'..π, |(f (x - y) - f x) * K N y|) := by rw [h_split]
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y|)
          + (∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y|)
          + ∫ y in δ'..π, |f (x - y) - f x| * |K N y|) := by simp_rw [abs_mul]
      _ ≤ 1 / (2 * π) * (2 * C * (∫ y in (-π)..(-δ'), |K N y|)
          + ε * π / (M + 1) * M
          + 2 * C * (∫ y in δ'..π, |K N y|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_near_bound := h_near.trans (mul_le_mul_of_nonneg_left h_near_K_le (by positivity))
          linarith [h_far1, h_far2, h_near_bound]
      _ = 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|)) := by ring
      _ ≤ 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * (ε * π / (2 * C + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [htail_bound]
      _ ≤ ε := by
          have h1 : 0 < M + 1 := by linarith
          have h2 : 0 < 2 * C + 1 := by linarith
          have key : ε * π / (M + 1) * M + 2 * C * (ε * π / (2 * C + 1)) =
              ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)) := by field_simp
          rw [key]
          calc 1 / (2 * π) * (ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)))
              ≤ 1 / (2 * π) * (ε * π * 2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith [show M / (M + 1) ≤ 1 from by rw [div_le_one h1]; linarith,
                          show 2 * C / (2 * C + 1) ≤ 1 from by rw [div_le_one h2]; linarith]
            _ = ε := by field_simp

end ApproximateIdentity

end

open ContinuousMap Set

namespace TrigPolyDensity

variable {T : ℝ} [hT : Fact (0 < T)]

theorem trigPoly_dense_in_continuous :
    Dense ((Submodule.span ℂ (range (@fourier T))) : Set C(AddCircle T, ℂ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact span_fourier_closure_eq_top

theorem trigPoly_approx_sup_norm (f : C(AddCircle T, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ (Submodule.span ℂ (range (@fourier T)) : Set C(AddCircle T, ℂ)),
      ‖f - p‖ < ε := by
  obtain ⟨p, hball, hmem⟩ := Metric.dense_iff.mp trigPoly_dense_in_continuous f ε hε
  exact ⟨p, hmem, by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hball⟩

end TrigPolyDensity

open MeasureTheory Filter Topology Set intervalIntegral Real

noncomputable section

namespace FejerL1Density

def periodicL1Norm (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-π)..π, |f x|

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

def fejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  if N = 0 then 0
  else if sin (x / 2) = 0 then (N : ℝ)
  else (1 / N : ℝ) * (sin (N * x / 2) / sin (x / 2)) ^ 2

def fejerMean (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  periodicConvolution f (fejerKernel N)

def IsTrigPolynomial (p : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (a b : ℕ → ℝ),
    ∀ x, p x = ∑ n ∈ Finset.range (N + 1),
      (a n * cos (n * x) + b n * sin (n * x))

lemma periodicL1Norm_nonneg (f : ℝ → ℝ) : 0 ≤ periodicL1Norm f := by
  unfold periodicL1Norm
  apply mul_nonneg (by positivity)
  exact integral_nonneg (by linarith [pi_pos]) (fun u _ => abs_nonneg _)

lemma periodicL1Norm_sub_comm (f g : ℝ → ℝ) :
    periodicL1Norm (fun x => f x - g x) = periodicL1Norm (fun x => g x - f x) := by
  unfold periodicL1Norm; congr 1; congr 1; ext x; exact abs_sub_comm (f x) (g x)


set_option maxHeartbeats 400000 in
lemma abs_sin_mul_le (n : ℕ) (θ : ℝ) : |sin (n * θ)| ≤ n * |sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc |sin (↑n * θ) * cos θ + cos (↑n * θ) * sin θ|
        ≤ |sin (↑n * θ)| * |cos θ| + |cos (↑n * θ)| * |sin θ| := by
          exact le_trans (abs_add_le _ _) (by rw [abs_mul, abs_mul])
      _ ≤ ↑n * |sin θ| * 1 + 1 * |sin θ| := by
          linarith [mul_le_mul ih (abs_cos_le_one θ) (abs_nonneg _)
                      (by positivity : 0 ≤ ↑n * |sin θ|),
                     mul_le_mul_of_nonneg_right (abs_cos_le_one (↑n * θ)) (abs_nonneg (sin θ))]
      _ = (↑n + 1) * |sin θ| := by ring


lemma fejerKernel_measurable (N : ℕ) : Measurable (fejerKernel N) := by
  unfold fejerKernel
  by_cases hN : N = 0
  · simp [hN]
  · simp only [hN, ↓reduceIte]
    apply Measurable.ite
    · exact (isClosed_eq (continuous_sin.comp (continuous_id.div_const 2))
        continuous_const).measurableSet
    · exact measurable_const
    · exact ((measurable_sin.comp ((measurable_const.mul measurable_id).div_const 2)).div
        (measurable_sin.comp (measurable_id.div_const 2))).pow measurable_const
        |>.const_mul _


lemma fejerKernel_nonneg_aux (N : ℕ) (x : ℝ) : 0 ≤ fejerKernel N x := by
  unfold fejerKernel
  split_ifs <;> [exact le_refl 0; exact Nat.cast_nonneg N;
    exact mul_nonneg (by positivity) (sq_nonneg _)]


set_option maxHeartbeats 400000 in
lemma fejerKernel_le_N (N : ℕ) (x : ℝ) : fejerKernel N x ≤ N := by
  unfold fejerKernel
  split_ifs with h0 hs
  · simp [h0]
  · exact le_refl _
  · have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h0
    have key : |sin (↑N * x / 2) / sin (x / 2)| ≤ N := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
      rw [show ↑N * x / 2 = ↑N * (x / 2) from by ring]
      exact abs_sin_mul_le N (x / 2)
    have hbound : (sin (↑N * x / 2) / sin (x / 2)) ^ 2 ≤ (↑N) ^ 2 := by
      rw [← sq_abs (sin (↑N * x / 2) / sin (x / 2))]
      exact pow_le_pow_left₀ (abs_nonneg _) key 2
    calc (1 / ↑N) * (sin (↑N * x / 2) / sin (x / 2)) ^ 2
        ≤ (1 / ↑N) * ↑N ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ↑N := by field_simp


lemma fejerKernel_intervalIntegrable (N : ℕ) :
    IntervalIntegrable (fejerKernel N) volume (-π) π := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
  apply Measure.integrableOn_of_bounded
  · exact measure_Ioc_lt_top.ne
  · exact (fejerKernel_measurable N).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N x)]
    exact fejerKernel_le_N N x


lemma integral_cos_nat_mul_eq_zero (k : ℕ) (hk : k ≠ 0) :
    ∫ x in (-π)..π, cos (↑k * x) = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have : (fun x => cos (↑k * x)) = (fun x => cos (x * ↑k)) := by ext x; ring
  rw [this, integral_comp_mul_right cos hk_ne, integral_cos, neg_mul, sin_neg]
  have h_sin : sin (π * ↑k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  simp [h_sin]


lemma integral_const_mul_cos_eq_zero (c : ℝ) (k : ℕ) :
    ∫ x in (-π)..π, c * cos ((↑k + 1) * x) = 0 := by
  rw [show (fun x => c * cos ((↑k + 1) * x)) = (fun x => c * cos (↑(k + 1) * x)) from by
    ext x; push_cast; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cos_nat_mul_eq_zero (k + 1) (by omega)]
  simp


lemma two_sin_half_mul_cos (k : ℕ) (x : ℝ) :
    2 * sin (x / 2) * cos (↑k * x) =
      sin ((2 * ↑k + 1) * (x / 2)) - sin ((2 * ↑k - 1) * (x / 2)) := by
  have h1 : sin ((2 * ↑k + 1) * (x / 2)) = sin (↑k * x + x / 2) := by ring_nf
  have h2 : sin ((2 * ↑k - 1) * (x / 2)) = sin (↑k * x - x / 2) := by ring_nf
  rw [h1, h2, sin_add, sin_sub]; ring


lemma dirichlet_identity (n : ℕ) (x : ℝ) :
    sin ((2 * ↑n + 1) * (x / 2)) =
      sin (x / 2) + 2 * sin (x / 2) * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih]
    push_cast
    have h := two_sin_half_mul_cos (m + 1) x
    push_cast at h
    have key : (2 * (↑m + 1) - 1 : ℝ) = 2 * ↑m + 1 := by ring
    rw [key] at h
    linarith


lemma fejer_telescope (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, sin ((2 * ↑n + 1) * (x / 2)) * sin (x / 2) =
      sin (↑N * x / 2) ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]; push_cast
    have h_prod : 2 * sin ((2 * ↑m + 1) * (x / 2)) * sin (x / 2) =
        cos (↑m * x) - cos ((↑m + 1) * x) := by
      have := cos_sub_cos (↑m * x) ((↑m + 1) * x)
      have h1 : (↑m * x + (↑m + 1) * x) / 2 = (2 * ↑m + 1) * (x / 2) := by ring
      have h2 : (↑m * x - (↑m + 1) * x) / 2 = -(x / 2) := by ring
      rw [h1, h2, sin_neg] at this; linarith
    have h_cos1 : cos (↑m * x) = 1 - 2 * sin (↑m * x / 2) ^ 2 := by
      rw [show ↑m * x = 2 * (↑m * x / 2) from by ring, cos_two_mul, sin_sq]; ring
    have h_cos2 : cos ((↑m + 1) * x) = 1 - 2 * sin ((↑m + 1) * x / 2) ^ 2 := by
      rw [show (↑m + 1) * x = 2 * ((↑m + 1) * x / 2) from by ring, cos_two_mul, sin_sq]; ring
    nlinarith


lemma sin_half_ne_zero_of_ne_zero {x : ℝ} (hx : x ∈ Ioc (-π) π) (hx0 : x ≠ 0) :
    sin (x / 2) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
  have hx_eq : x = 2 * ↑n * π := by linarith
  have hpi := pi_pos
  have h1 : -(1 : ℤ) < 2 * n := by
    by_contra hc; push_neg at hc
    have : (2 * (n : ℝ)) ≤ -1 := by exact_mod_cast hc
    nlinarith [hx.1]
  have h2 : 2 * n ≤ (1 : ℤ) := by
    by_contra hc; push_neg at hc
    have : (2 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hc
    nlinarith [hx.2]
  exact hx0 (by rw [hx_eq]; simp [show n = 0 from by omega])


lemma integral_dirichlet_sum (n : ℕ) :
    ∫ x in (-π)..π, (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = 2 * π := by
  induction n with
  | zero => simp [intervalIntegral.integral_const, smul_eq_mul]; ring
  | succ m ih =>
    have h_rw : (fun x => 1 + 2 * ∑ k ∈ Finset.range (m + 1), cos ((↑k + 1) * x)) =
      (fun x => (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) +
        2 * cos ((↑m + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]; ring
    rw [h_rw, intervalIntegral.integral_add]
    · rw [integral_const_mul_cos_eq_zero 2 m, add_zero, ih]
    · exact (Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finset_sum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
    · exact ((continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _).const_mul _


lemma integral_fejer_sum_all (N : ℕ) :
    ∫ x in (-π)..π, ∑ n ∈ Finset.range N,
      (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = ↑N * (2 * π) := by
  induction N with
  | zero => simp
  | succ m ih =>
    have h_rw : (fun x => ∑ n ∈ Finset.range (m + 1),
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) =
      fun x => (∑ n ∈ Finset.range m,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) +
        (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]
    have h_cts : ∀ n : ℕ, Continuous (fun x =>
        (1 : ℝ) + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) :=
      fun n => Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finset_sum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))
    rw [h_rw, intervalIntegral.integral_add
      ((continuous_finset_sum _ (fun n _ => h_cts n)).intervalIntegrable _ _)
      ((h_cts m).intervalIntegrable _ _)]
    rw [ih, integral_dirichlet_sum]; push_cast; ring


set_option maxHeartbeats 1600000 in
theorem fejerKernel_normalize (N : ℕ) (hN : N ≠ 0) :
    (1 / (2 * π)) * ∫ x in (-π)..π, fejerKernel N x = 1 := by
  have h_ae : ∀ᵐ (x : ℝ) ∂volume, x ∈ uIoc (-π) π →
      fejerKernel N x = (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) := by
    have h_ne : ∀ᵐ (x : ℝ) ∂volume, x ≠ 0 := by
      rw [Filter.eventually_iff, mem_ae_iff]
      show volume {x : ℝ | ¬x ≠ 0} = 0
      have : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by ext x; simp
      rw [this]; exact Real.volume_singleton
    filter_upwards [h_ne] with x hx0 hx_mem
    have hx' : x ∈ Ioc (-π) π := by rwa [uIoc_of_le (by linarith [pi_pos])] at hx_mem
    have hsin : sin (x / 2) ≠ 0 := sin_half_ne_zero_of_ne_zero hx' hx0
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    congr 1
    rw [div_pow, ← fejer_telescope N x, Finset.sum_div]
    congr 1; ext n
    rw [dirichlet_identity n x]; field_simp
  rw [integral_congr_ae h_ae, intervalIntegral.integral_const_mul, integral_fejer_sum_all N]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpi : π ≠ 0 := ne_of_gt pi_pos
  field_simp


noncomputable instance : Fact (0 < (2 * π : ℝ)) := ⟨by positivity⟩

set_option maxHeartbeats 3200000 in
theorem continuous_periodic_dense_L1
    (f : ℝ → ℝ) (hf_periodic : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    ∀ ε > 0, ∃ g : ℝ → ℝ,
      Continuous g ∧ Function.Periodic g (2 * π) ∧
      periodicL1Norm (fun x => f x - g x) ≤ ε := by
  intro ε hε
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]

  have hf_int : Integrable f (volume.restrict (Icc (-π) π)) := by
    rw [IntervalIntegrable] at hf_intble; change IntegrableOn f (Icc (-π) π) volume
    rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hf_intble.1

  obtain ⟨g₀, _, hg₀_close, hg₀_cont, _⟩ :=
    hf_int.exists_hasCompactSupport_integral_sub_le (show (0:ℝ) < ε * π by positivity)

  obtain ⟨M_pt, _, hM_pt⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hpi_le)
    ((continuous_abs.comp hg₀_cont).continuousOn : ContinuousOn (|g₀ ·|) (Icc (-π) π))
  set M := |g₀ M_pt|
  have hM_bound : ∀ x ∈ Icc (-π) π, |g₀ x| ≤ M := fun x hx => hM_pt hx

  set δ := min π (ε * π / (2 * (M + 1)))
  have hδ_pos : 0 < δ := by positivity
  let tent : ℝ → ℝ := fun x => max 0 (min 1 ((π - |x|) / δ))
  have tent_cont : Continuous tent :=
    continuous_const.max (continuous_const.min ((continuous_const.sub continuous_abs).div_const δ))

  set g₁ := fun x => g₀ x * tent x
  have hg₁_cont : Continuous g₁ := hg₀_cont.mul tent_cont
  have tent_zero_at : ∀ x : ℝ, π ≤ |x| → tent x = 0 :=
    fun x hx => max_eq_left_iff.mpr
      (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ_pos.le))
  have hg₁_pi : g₁ π = 0 := by
    show g₀ π * tent π = 0
    rw [tent_zero_at π (by simp [abs_of_pos pi_pos])]; ring
  have hg₁_neg_pi : g₁ (-π) = 0 := by
    show g₀ (-π) * tent (-π) = 0
    rw [tent_zero_at (-π) (by simp [abs_of_pos pi_pos])]; ring
  have hg₁_match : g₁ (-π) = g₁ (-π + 2 * π) := by
    rw [show (-π : ℝ) + 2 * π = π from by ring, hg₁_neg_pi, hg₁_pi]

  let gc := AddCircle.liftIco (2 * π) (-π) g₁
  have hgc_cont : Continuous gc := AddCircle.liftIco_continuous hg₁_match
    (by rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hg₁_cont.continuousOn)
  let g := fun x : ℝ => gc ((x : AddCircle (2 * π)))
  have hg_cont : Continuous g := hgc_cont.comp (AddCircle.continuous_mk' (2 * π))
  have hg_per : Function.Periodic g (2 * π) := fun x => by simp [g]

  have hg_eq : ∀ x ∈ Ico (-π) π, g x = g₁ x := fun x hx =>
    AddCircle.liftIco_coe_apply
      (show x ∈ Ico (-π) (-π + 2 * π) by rwa [show (-π : ℝ) + 2 * π = π from by ring])

  refine ⟨g, hg_cont, hg_per, ?_⟩
  simp only [periodicL1Norm]

  have hg₀_int : ∫ x in (-π)..π, |f x - g₀ x| ≤ ε * π := by
    have h1 : ∫ x in (-π)..π, |f x - g₀ x| = ∫ x in Icc (-π) π, ‖f x - g₀ x‖ := by
      simp only [Real.norm_eq_abs]
      rw [intervalIntegral.integral_of_le hpi_le, ← integral_Icc_eq_integral_Ioc]
    linarith

  have hfg_eq : ∀ᵐ x ∂volume, x ∈ uIoc (-π) π →
      |(fun x => f x - g x) x| = |f x - g₁ x| := by
    apply ae_of_all; intro x hx
    rw [uIoc_of_le hpi_le] at hx

    suffices hgx : g x = g₁ x by show |f x - g x| = |f x - g₁ x|; rw [hgx]
    by_cases hxπ : x = π
    · subst hxπ

      have h1 : g π = g (-π) := by
        show gc ((π : ℝ) : AddCircle (2 * π)) = gc ((-π : ℝ) : AddCircle (2 * π))
        congr 1
        rw [QuotientAddGroup.eq]; exact ⟨-1, by simp [zsmul_eq_mul]; ring⟩

      rw [h1, hg_eq (-π) ⟨le_refl _, by linarith [pi_pos]⟩, hg₁_neg_pi, hg₁_pi]

    · exact hg_eq x ⟨hx.1.le, lt_of_le_of_ne hx.2 hxπ⟩
  rw [intervalIntegral.integral_congr_ae hfg_eq]

  have htri : ∀ x, |f x - g₁ x| ≤ |f x - g₀ x| + |g₀ x - g₁ x| := by
    intro x; calc |f x - g₁ x| = |(f x - g₀ x) + (g₀ x - g₁ x)| := by ring_nf
      _ ≤ |f x - g₀ x| + |g₀ x - g₁ x| := abs_add_le _ _

  have hδ_le : δ ≤ ε * π / (2 * (M + 1)) := min_le_right _ _
  have hg₀g₁ : ∫ x in (-π)..π, |g₀ x - g₁ x| ≤ ε * π := by


    have habs_cont : Continuous (fun x => |g₀ x - g₁ x|) := (hg₀_cont.sub hg₁_cont).abs
    have hint := habs_cont.intervalIntegrable (-π) π (μ := volume)
    have hint1 := habs_cont.intervalIntegrable (-π) (-π + δ) (μ := volume)
    have hint2 := habs_cont.intervalIntegrable (-π + δ) (π - δ) (μ := volume)
    have hint3 := habs_cont.intervalIntegrable (π - δ) π (μ := volume)


    have tent_one : ∀ x, |x| ≤ π - δ → tent x = 1 := by
      intro x hx
      show max 0 (min 1 ((π - |x|) / δ)) = 1
      have h1 : 1 ≤ (π - |x|) / δ := by rw [le_div_iff₀ hδ_pos]; linarith
      simp only [min_eq_left h1, max_eq_right (by linarith : (0:ℝ) ≤ 1)]
    have mid_zero : ∫ x in (-π + δ)..(π - δ), |g₀ x - g₁ x| = 0 := by
      have hzero : ∀ᵐ x ∂volume, x ∈ uIoc (-π + δ) (π - δ) →
          |g₀ x - g₁ x| = (0 : ℝ) := by
        apply ae_of_all; intro x hx
        have hδ_le_pi : δ ≤ π := min_le_left _ _
        rw [uIoc_of_le (by linarith [pi_pos])] at hx

        have habs : |x| ≤ π - δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have : g₁ x = g₀ x * tent x := rfl
        rw [this, tent_one x habs, mul_one, sub_self, abs_zero]
      rw [intervalIntegral.integral_congr_ae hzero]
      simp


    have bound_pw : ∀ x ∈ Icc (-π) π, |g₀ x - g₁ x| ≤ M := by
      intro x hx
      have : g₁ x = g₀ x * tent x := rfl
      rw [this, show g₀ x - g₀ x * tent x = g₀ x * (1 - tent x) from by ring, abs_mul]
      calc |g₀ x| * |1 - tent x|
          ≤ M * 1 := by
            apply mul_le_mul (hM_bound x hx)
            ·
              have ht0 : 0 ≤ tent x := le_max_left 0 _
              have ht1 : tent x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
              rw [abs_of_nonneg (by linarith)]
              linarith
            · exact abs_nonneg _
            · exact abs_nonneg _
        _ = M := mul_one M


    rw [show (-π : ℝ) = -π from rfl,
        ← intervalIntegral.integral_add_adjacent_intervals hint1
          (hint2.trans hint3),
        ← intervalIntegral.integral_add_adjacent_intervals hint2 hint3,
        mid_zero, zero_add]

    have hbd1 : ∫ x in (-π)..(-π + δ), |g₀ x - g₁ x| ≤ M * δ := by
      calc ∫ x in (-π)..(-π + δ), |g₀ x - g₁ x|
          ≤ ∫ x in (-π)..(-π + δ), (M : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith [hδ_pos]) hint1
              _root_.intervalIntegrable_const
            intro x hx
            have hδ_le_pi : δ ≤ π := min_le_left _ _
            exact bound_pw x ⟨hx.1, by linarith [hx.2]⟩

        _ = M * δ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hbd2 : ∫ x in (π - δ)..π, |g₀ x - g₁ x| ≤ M * δ := by
      calc ∫ x in (π - δ)..π, |g₀ x - g₁ x|
          ≤ ∫ x in (π - δ)..π, (M : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith [hδ_pos]) hint3
              _root_.intervalIntegrable_const
            intro x hx
            have hδ_le_pi : δ ≤ π := min_le_left _ _
            exact bound_pw x ⟨by linarith [hx.1], hx.2⟩

        _ = M * δ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring

    calc (∫ x in (-π)..(-π + δ), |g₀ x - g₁ x|) + ∫ x in (π - δ)..π, |g₀ x - g₁ x|
        ≤ M * δ + M * δ := add_le_add hbd1 hbd2
      _ = 2 * M * δ := by ring
      _ ≤ 2 * M * (ε * π / (2 * (M + 1))) := by
          apply mul_le_mul_of_nonneg_left hδ_le (by positivity)
      _ = M / (M + 1) * (ε * π) := by field_simp

      _ ≤ 1 * (ε * π) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by positivity)]; linarith [abs_nonneg (g₀ M_pt)]
      _ = ε * π := one_mul _

  calc 1 / (2 * π) * ∫ x in (-π)..π, |f x - g₁ x|
      ≤ 1 / (2 * π) * ((∫ x in (-π)..π, |f x - g₀ x|) + ∫ x in (-π)..π, |g₀ x - g₁ x|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∫ x in (-π)..π, |f x - g₁ x|
            ≤ ∫ x in (-π)..π, (|f x - g₀ x| + |g₀ x - g₁ x|) :=
              intervalIntegral.integral_mono_on hpi_le
                (hf_intble.sub (hg₁_cont.intervalIntegrable _ _)).abs
                ((hf_intble.sub (hg₀_cont.intervalIntegrable _ _)).abs.add
                  ((hg₀_cont.sub hg₁_cont).intervalIntegrable _ _).abs)
                (fun x _ => htri x)
          _ = _ := by
              rw [intervalIntegral.integral_add
                (hf_intble.sub (hg₀_cont.intervalIntegrable _ _)).abs
                ((hg₀_cont.sub hg₁_cont).intervalIntegrable _ _).abs]
    _ ≤ 1 / (2 * π) * (ε * π + ε * π) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hg₀_int hg₀g₁) (by positivity)
    _ = ε := by have : π ≠ 0 := ne_of_gt pi_pos; field_simp; ring


lemma periodic_integral_translate_abs (h : ℝ → ℝ)
    (hper : Function.Periodic h (2 * π)) (y : ℝ) :
    ∫ x in (-π)..π, |h (x - y)| = ∫ x in (-π)..π, |h x| := by
  have habs_per : Function.Periodic (|h ·|) (2 * π) := fun x => by
    show |h (x + 2 * π)| = |h x|; rw [hper x]
  rw [integral_comp_sub_right (fun x => |h x|) y]
  convert habs_per.intervalIntegral_add_eq (-π - y) (-π) using 2 <;> ring


lemma fubini_conv_eq (h : ℝ → ℝ) (N : ℕ)
    (hh_per : Function.Periodic h (2 * π))
    (hint : Integrable (Function.uncurry fun x y =>
        |h (x - y)| * fejerKernel N y)
      ((volume.restrict (Ioc (-π : ℝ) π)).prod
       (volume.restrict (Ioc (-π : ℝ) π)))) :
    ∫ x, (∫ y, |h (x - y)| * fejerKernel N y
      ∂(volume.restrict (Ioc (-π : ℝ) π)))
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
    (∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π))) *
    (∫ y, fejerKernel N y ∂(volume.restrict (Ioc (-π : ℝ) π))) := by
  rw [integral_integral_swap hint]
  have hfact : ∀ y, ∫ x, |h (x - y)| * fejerKernel N y
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
      fejerKernel N y * ∫ x, |h (x - y)|
      ∂(volume.restrict (Ioc (-π : ℝ) π)) := by
    intro y
    rw [show (fun x => |h (x - y)| * fejerKernel N y) =
      (fun x => fejerKernel N y * |h (x - y)|) from by ext; ring]
    exact integral_const_mul _ _
  simp_rw [hfact]
  have htrans : ∀ y, ∫ x, |h (x - y)|
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
      ∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π)) := by
    intro y
    rw [← integral_of_le (by linarith [pi_pos] : (-π : ℝ) ≤ π),
        ← integral_of_le (by linarith [pi_pos] : (-π : ℝ) ≤ π)]
    exact periodic_integral_translate_abs h hh_per y
  simp_rw [htrans, mul_comm (fejerKernel N _)]
  exact integral_const_mul _ _

set_option maxHeartbeats 3200000 in
theorem young_fejerKernel (h : ℝ → ℝ) (N : ℕ)
    (hh : IntervalIntegrable h volume (-π) π)
    (hh_per : Function.Periodic h (2 * π)) :
    periodicL1Norm (periodicConvolution h (fejerKernel N)) ≤ periodicL1Norm h := by

  by_cases hN : N = 0
  · subst hN
    have h1 : fejerKernel 0 = fun _ => (0 : ℝ) := by ext x; unfold fejerKernel; simp
    rw [h1]
    have h2 : periodicConvolution h (fun _ => 0) = fun _ => 0 := by
      ext x; unfold periodicConvolution; simp
    rw [h2, show periodicL1Norm (fun _ => (0 : ℝ)) = 0 from by unfold periodicL1Norm; simp]
    exact periodicL1Norm_nonneg h

  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  unfold periodicL1Norm periodicConvolution
  apply mul_le_mul_of_nonneg_left _ (by positivity)


  have pw_bound : ∀ x, |1 / (2 * π) * ∫ y in (-π)..π, h (x - y) * fejerKernel N y| ≤
      1 / (2 * π) * ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
    intro x
    rw [abs_mul, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc |∫ y in (-π)..π, h (x - y) * fejerKernel N y|
        ≤ ∫ y in (-π)..π, |h (x - y) * fejerKernel N y| := by
          have := @norm_integral_le_integral_norm ℝ _ _ (-π) π
            (fun y => h (x - y) * fejerKernel N y) volume hpi
          simp only [Real.norm_eq_abs] at this; exact this
      _ = ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
          congr 1; ext y; rw [abs_mul, abs_of_nonneg (fejerKernel_nonneg_aux N y)]


  have conv_to_restrict : ∀ (f : ℝ → ℝ),
      ∫ x in (-π : ℝ)..π, f x = ∫ x, f x ∂(volume.restrict (Ioc (-π : ℝ) π)) :=
    fun f => integral_of_le hpi


  have hint : Integrable (Function.uncurry fun x y =>
      |h (x - y)| * fejerKernel N y)
    ((volume.restrict (Ioc (-π : ℝ) π)).prod
     (volume.restrict (Ioc (-π : ℝ) π))) := by

    have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
    have habs_per : Function.Periodic (fun z => |h z|) (2 * π) := by intro z; simp [hh_per z]
    have hf_any : ∀ a b : ℝ, IntervalIntegrable h volume a b :=
      hh_per.intervalIntegrable h2pi (t := -π)
        (show IntervalIntegrable h volume (-π) (-π + 2 * π) from by
          rwa [show (-π : ℝ) + 2 * π = π from by ring])
    have hf_loc : LocallyIntegrable h volume := by
      intro x; exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
        (hf_any (x - 2) (x + 1)).1.mono_set (fun y hy => ⟨by linarith [hy.1], hy.2⟩)⟩
    obtain ⟨g, hg_sm, hfg⟩ := hf_loc.aestronglyMeasurable

    have hprod_aesm : AEStronglyMeasurable
        (Function.uncurry fun x y => |h (x - y)| * fejerKernel N y)
        ((volume.restrict (Ioc (-π : ℝ) π)).prod (volume.restrict (Ioc (-π : ℝ) π))) := by
      refine ((hg_sm.comp_measurable (measurable_fst.sub measurable_snd)).norm.mul
        ((fejerKernel_measurable N).stronglyMeasurable.comp_measurable
          measurable_snd)).aestronglyMeasurable.congr ?_
      filter_upwards [(hfg.comp_tendsto
        (quasiMeasurePreserving_sub (volume : Measure ℝ) volume).tendsto_ae).filter_mono
        (Measure.AbsolutelyContinuous.prod
          (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := Ioc (-π) π)))
          (Measure.absolutelyContinuous_of_le
            (Measure.restrict_le_self (s := Ioc (-π) π)))).ae_le]
        with ⟨a, b⟩ heq
      simp only [Function.uncurry, Function.comp, Pi.mul_apply] at heq ⊢
      rw [Real.norm_eq_abs, heq]

    have hslice : ∀ x, IntegrableOn (fun y => |h (x - y)| * fejerKernel N y)
        (Ioc (-π : ℝ) π) volume := by
      intro x
      have habs_x : IntervalIntegrable (fun y => |h (x - y)|) volume (-π) π := by
        have habs_ii := habs_per.intervalIntegrable h2pi (t := -π)
          (show IntervalIntegrable (fun z => |h z|) volume (-π) (-π + 2 * π) from by
            rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hh.abs)
        convert (habs_ii (x + π) (x - π)).comp_sub_left x using 1 <;> ring
      exact ((habs_x.1 |>.mono_set Subset.rfl).bdd_mul (fejerKernel_measurable N).aestronglyMeasurable.restrict
        (Eventually.of_forall fun y => by
          simp only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N y)]
          exact fejerKernel_le_N N y)).congr (Eventually.of_forall fun y => by ring)
    rw [integrable_prod_iff hprod_aesm]
    refine ⟨Eventually.of_forall fun x => hslice x, ?_⟩

    haveI : IsFiniteMeasure (volume.restrict (Ioc (-π : ℝ) π)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    rw [← integrableOn_univ]
    apply Measure.integrableOn_of_bounded (measure_ne_top _ _)
      (hprod_aesm.norm.integral_prod_right')
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    calc ∫ y in Ioc (-π) π, ‖(Function.uncurry fun x y =>
            |h (x - y)| * fejerKernel N y) (x, y)‖
        = ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
          rw [integral_of_le hpi]; congr 1; ext y
          simp only [Function.uncurry, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (abs_nonneg _) (fejerKernel_nonneg_aux N y))]
      _ ≤ ↑N * ∫ y in (-π)..π, |h y| := by
          have habs_x : IntervalIntegrable (fun y => |h (x - y)|) volume (-π) π := by
            have habs_ii := habs_per.intervalIntegrable h2pi (t := -π)
              (show IntervalIntegrable (fun z => |h z|) volume (-π) (-π + 2 * π) from by
                rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hh.abs)
            convert (habs_ii (x + π) (x - π)).comp_sub_left x using 1 <;> ring
          have hslice_ii : IntervalIntegrable
              (fun y => |h (x - y)| * fejerKernel N y) volume (-π) π := by
            rw [intervalIntegrable_iff, uIoc_of_le hpi]; exact hslice x
          calc ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y
              ≤ ∫ y in (-π)..π, |h (x - y)| * ↑N := by
                apply integral_mono_on hpi hslice_ii (habs_x.mul_const _)
                intro y _; exact mul_le_mul_of_nonneg_left (fejerKernel_le_N N y) (abs_nonneg _)
            _ = ↑N * ∫ y in (-π)..π, |h (x - y)| := by
                rw [show (fun y => |h (x - y)| * ↑N) = (fun y => ↑N * |h (x - y)|)
                  from by ext; ring]; exact intervalIntegral.integral_const_mul _ _
            _ = ↑N * ∫ y in (-π)..π, |h y| := by
                congr 1; rw [integral_comp_sub_left (fun y => |h y|) x]
                convert habs_per.intervalIntegral_add_eq (x - π) (-π) using 2 <;> ring

  have hbound_intble : IntervalIntegrable
      (fun u => 1 / (2 * π) * ∫ y in (-π)..π, |h (u - y)| * fejerKernel N y) volume (-π) π := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    have := hint.integral_prod_left
    rwa [show (fun x => ∫ y, (Function.uncurry fun x y => |h (x - y)| * fejerKernel N y) (x, y)
        ∂(volume.restrict (Ioc (-π : ℝ) π))) =
      (fun x => ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) from by
        ext x; rw [← integral_of_le hpi]; rfl] at this

  calc ∫ x in (-π)..π, |1 / (2 * π) * ∫ y in (-π)..π, h (x - y) * fejerKernel N y|
      ≤ ∫ x in (-π)..π, (1 / (2 * π) * ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) := by

        rw [conv_to_restrict, conv_to_restrict]
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun x => abs_nonneg _
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hbound_intble
        · exact ae_of_all _ fun x => pw_bound x
    _ = 1 / (2 * π) * ∫ x in (-π)..π, (∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) := by
        rw [← intervalIntegral.integral_const_mul]
    _ = 1 / (2 * π) * ((∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π))) *
        (∫ y, fejerKernel N y ∂(volume.restrict (Ioc (-π : ℝ) π)))) := by
        congr 1
        simp_rw [conv_to_restrict]
        exact fubini_conv_eq h N hh_per hint
    _ = ∫ x in (-π)..π, |h x| := by
        rw [← conv_to_restrict, ← conv_to_restrict]
        rw [show (1 / (2 * π) * ((∫ x in (-π)..π, |h x|) *
            (∫ y in (-π)..π, fejerKernel N y))) =
            (∫ x in (-π)..π, |h x|) * (1 / (2 * π) *
            (∫ y in (-π)..π, fejerKernel N y)) from by ring]
        rw [fejerKernel_normalize N hN, mul_one]


set_option maxHeartbeats 3200000 in
theorem fejer_uniform_convergence (g : ℝ → ℝ)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel N) x| ≤ ε := by
  suffices key : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel (n + 1)) x| ≤ ε by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := key ε hε
    exact ⟨N₀ + 1, fun N hN x => by
      have : N = (N - 1) + 1 := by omega
      rw [this]; exact hN₀ (N - 1) (by omega) x⟩
  apply ApproximateIdentity.approximate_identity_lemma g (fun n => fejerKernel (n + 1)) hg_cont hg_per

  · intro N; exact fejerKernel_intervalIntegrable (N + 1)

  · intro N x
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).continuousOn)

  · intro N
    have : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [this]; exact fejerKernel_intervalIntegrable (N + 1)

  · intro N x
    have h_eq : (fun y => |g (x - y) - g x| * |fejerKernel (N + 1) y|) =
        fun y => |g (x - y) - g x| * fejerKernel (N + 1) y := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [h_eq]
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).sub continuous_const).abs.continuousOn

  · intro N; exact fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)

  · refine ⟨2 * π, fun N => ?_⟩
    have hab : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [hab]
    have h_norm := fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)
    have hI : ∫ x in (-π)..π, fejerKernel (N + 1) x = 2 * π := by
      have : (0 : ℝ) < 2 * π := by positivity
      field_simp at h_norm; linarith
    linarith

  · intro δ hδ_pos hδ_le_pi
    have hpi_pos := pi_pos
    have hδ2_pos : 0 < δ / 2 := by linarith
    have hδ2_lt_pi : δ / 2 < π := by linarith
    have hsin_δ_pos : 0 < sin (δ / 2) := sin_pos_of_pos_of_lt_pi hδ2_pos hδ2_lt_pi
    have hsin_δ_sq_pos : 0 < sin (δ / 2) ^ 2 := sq_pos_of_pos hsin_δ_pos

    have h_abs_eq : ∀ n, (fun x => |fejerKernel (n + 1) x|) = fejerKernel (n + 1) := fun n => by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (n + 1) y)]
    simp_rw [h_abs_eq]

    set C : ℕ → ℝ := fun n => 1 / ((n + 1 : ℝ) * sin (δ / 2) ^ 2) with hC_def

    have h_pw_pos : ∀ n, ∀ x ∈ Icc δ π, fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hx_half_pos : 0 < x / 2 := by linarith [lt_of_lt_of_le hδ_pos hxl]
      have hx_half_le : x / 2 ≤ π / 2 := by linarith
      have hsin_x_pos : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx_half_pos (by linarith)
      have hsin_x_ne : sin (x / 2) ≠ 0 := ne_of_gt hsin_x_pos
      have hsin_mono : sin (δ / 2) ≤ sin (x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx_half_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 :=
        sq_le_sq' (by linarith [sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)]) hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity


      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp

    have h_pw_neg : ∀ n, ∀ x ∈ Icc (-π) (-δ), fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hnx_pos : 0 < -x / 2 := by linarith
      have hnx_le : -x / 2 ≤ π / 2 := by linarith
      have hsin_nx_pos : 0 < sin (-x / 2) := sin_pos_of_pos_of_lt_pi hnx_pos (by linarith)
      have hsin_sq : sin (x / 2) ^ 2 = sin (-x / 2) ^ 2 := by
        rw [show -x / 2 = -(x / 2) from by ring, sin_neg]; ring
      have hsin_x_ne : sin (x / 2) ≠ 0 := by
        intro h; have := sq_eq_zero_iff.mpr h; rw [hsin_sq] at this
        linarith [sq_pos_of_pos hsin_nx_pos]
      have hsin_mono : sin (δ / 2) ≤ sin (-x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hnx_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 := by
        rw [hsin_sq]
        exact sq_le_sq' (by linarith [sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)]) hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp

    rw [Metric.tendsto_atTop]
    intro ε hε


    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (π - δ) / (ε * sin (δ / 2) ^ 2))
    use N₀
    intro n hn
    rw [Real.dist_eq, sub_zero]
    have hsum_nonneg : 0 ≤ (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) +
        ∫ x in δ..π, fejerKernel (n + 1) x := by
      apply add_nonneg
      · exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => fejerKernel_nonneg_aux (n+1) u)
      · exact intervalIntegral.integral_nonneg hδ_le_pi (fun u _ => fejerKernel_nonneg_aux (n+1) u)
    rw [abs_of_nonneg hsum_nonneg]

    have hC_bound : C n ≥ 0 := by simp only [hC_def]; positivity
    have h_bound_neg : ‖∫ x in (-π)..(-δ), fejerKernel (n + 1) x‖ ≤ C n * |(-δ) - (-π)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_neg n x
      rw [uIoc_of_le (by linarith : -π ≤ -δ)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have h_bound_pos : ‖∫ x in δ..π, fejerKernel (n + 1) x‖ ≤ C n * |π - δ| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_pos n x
      rw [uIoc_of_le hδ_le_pi] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have habs_neg : |-δ - -π| = π - δ := by rw [show -δ - -π = π - δ from by ring]; exact abs_of_nonneg (by linarith)
    have habs_pos : |π - δ| = π - δ := abs_of_nonneg (by linarith)
    rw [habs_neg] at h_bound_neg; rw [habs_pos] at h_bound_pos

    have h_neg_le : ∫ x in (-π)..(-δ), fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg (by linarith)
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_neg
    have h_pos_le : ∫ x in δ..π, fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg hδ_le_pi
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_pos

    have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) + ∫ x in δ..π, fejerKernel (n + 1) x
        ≤ C n * (π - δ) + C n * (π - δ) := add_le_add h_neg_le h_pos_le
      _ = 2 * (π - δ) * C n := by ring
      _ = 2 * (π - δ) / (((n : ℝ) + 1) * sin (δ / 2) ^ 2) := by simp only [hC_def]; ring
      _ < ε := by
          rw [div_lt_iff₀ (mul_pos hN_pos hsin_δ_sq_pos)]
          have hes := mul_pos hε hsin_δ_sq_pos
          have h1 : 2 * (π - δ) < ↑N₀ * (ε * sin (δ / 2) ^ 2) := by
            rwa [div_lt_iff₀ hes] at hN₀
          have h2 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h3 : ↑N₀ * (ε * sin (δ / 2) ^ 2) ≤ ↑n * (ε * sin (δ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right h2 hes.le
          nlinarith


theorem convolution_linear (g h : ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hg : IntervalIntegrable (fun y => g (x - y) * fejerKernel N y) volume (-π) π)
    (hh : IntervalIntegrable (fun y => h (x - y) * fejerKernel N y) volume (-π) π) :
    periodicConvolution (fun y => g y - h y) (fejerKernel N) x =
      periodicConvolution g (fejerKernel N) x -
        periodicConvolution h (fejerKernel N) x := by
  simp only [periodicConvolution, sub_mul, ← mul_sub]
  congr 1
  exact integral_sub hg hh


lemma conv_intble_of_continuous (g : ℝ → ℝ) (hg : Continuous g) (N : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y => g (x - y) * fejerKernel N y) volume (-π) π :=
  (fejerKernel_intervalIntegrable N).continuousOn_mul
    ((hg.comp (continuous_const.sub continuous_id)).continuousOn)


lemma conv_intble_of_periodic (f : ℝ → ℝ)
    (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π)
    (N : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y => f (x - y) * fejerKernel N y) volume (-π) π := by
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have hfx : IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
    have h := (hf_any (x + π) (x - π)).comp_sub_left x
    convert h using 1 <;> ring
  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hfx_io : IntegrableOn (fun y => f (x - y)) (uIoc (-π) π) volume := by
    rw [uIoc_of_le hpi]; exact hfx.1
  have hmul : IntegrableOn (fun y => fejerKernel N y * f (x - y)) (uIoc (-π) π) volume :=
    hfx_io.bdd_mul (fejerKernel_measurable N).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun y => by
        simp only [Real.norm_eq_abs]
        exact abs_le_abs (fejerKernel_le_N N y) (by linarith [fejerKernel_nonneg_aux N y]))
  rw [intervalIntegrable_iff]
  exact hmul.congr (Filter.Eventually.of_forall fun y => by ring)


lemma trig_sum_extend (a b : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M) (x : ℝ) :
    ∑ n ∈ Finset.range (N + 1), (a n * cos (↑n * x) + b n * sin (↑n * x)) =
    ∑ n ∈ Finset.range (M + 1),
      ((if n ≤ N then a n else 0) * cos (↑n * x) +
       (if n ≤ N then b n else 0) * sin (↑n * x)) := by
  have h_filter : (Finset.range (M + 1)).filter (fun n => n ≤ N) = Finset.range (N + 1) := by
    ext n; simp [Finset.mem_filter, Finset.mem_range]; omega
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (M + 1)) (fun n => n ≤ N)]
  rw [h_filter]
  have h_zero : ∑ n ∈ (Finset.range (M + 1)).filter (fun n => ¬(n ≤ N)),
      ((if n ≤ N then a n else 0) * cos (↑n * x) +
       (if n ≤ N then b n else 0) * sin (↑n * x)) = 0 := by
    apply Finset.sum_eq_zero; intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, not_le] at hn
    simp [show ¬(n ≤ N) from by omega]
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn; simp [show n ≤ N from by omega]


lemma isTrigPolynomial_add {p q : ℝ → ℝ}
    (hp : IsTrigPolynomial p) (hq : IsTrigPolynomial q) :
    IsTrigPolynomial (fun x => p x + q x) := by
  obtain ⟨N, a, b, hp⟩ := hp; obtain ⟨M, c, d, hq⟩ := hq
  refine ⟨max N M,
    fun n => (if n ≤ N then a n else 0) + (if n ≤ M then c n else 0),
    fun n => (if n ≤ N then b n else 0) + (if n ≤ M then d n else 0),
    fun x => ?_⟩
  simp only; rw [hp x, hq x]
  rw [trig_sum_extend a b N (max N M) (le_max_left N M) x]
  rw [trig_sum_extend c d M (max N M) (le_max_right N M) x]
  rw [← Finset.sum_add_distrib]; congr 1; ext n; ring


lemma isTrigPolynomial_smul (c : ℝ) {p : ℝ → ℝ}
    (hp : IsTrigPolynomial p) :
    IsTrigPolynomial (fun x => c * p x) := by
  obtain ⟨N, a, b, hp⟩ := hp
  exact ⟨N, fun n => c * a n, fun n => c * b n, fun x => by
    simp only; rw [hp x, Finset.mul_sum]; congr 1; ext n; ring⟩


lemma isTrigPolynomial_finset_sum {f : ℕ → ℝ → ℝ} {s : Finset ℕ}
    (hf : ∀ i ∈ s, IsTrigPolynomial (f i)) :
    IsTrigPolynomial (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨0, fun _ => 0, fun _ => 0, fun x => by simp⟩
  | cons a s ha ih =>
    rw [show (fun x => ∑ i ∈ Finset.cons a s ha, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) from by
      ext x; rw [Finset.sum_cons]]
    exact isTrigPolynomial_add (hf a (Finset.mem_cons_self a s))
      (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))


lemma dirichlet_isTrigPolynomial (j : ℕ) :
    IsTrigPolynomial (fun x => 1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
  refine ⟨j, fun n => if n = 0 then 1 else 2, fun _ => 0, fun x => ?_⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, cos_zero, ite_true, mul_one,
    Nat.succ_ne_zero, ite_false, add_zero]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  push_cast; ring


lemma cos_eq_one_of_sin_half_eq_zero (x : ℝ) (h : sin (x / 2) = 0) (n : ℕ) :
    cos (n * x) = 1 := by
  rw [sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hx : x = 2 * k * π := by linarith
  rw [hx, show (n : ℝ) * (2 * ↑k * π) = ↑(n * k) * (2 * π) from by push_cast; ring]
  exact cos_int_mul_two_pi (n * k)


private lemma sum_odd_eq_sq (N : ℕ) :
    ∑ j ∈ Finset.range N, ((1 : ℝ) + 2 * j) = N ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring


set_option maxHeartbeats 800000 in
lemma fejerKernel_eq_dirichlet_avg (N : ℕ) (hN : N ≠ 0) (x : ℝ) :
    fejerKernel N x =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
  by_cases hsin : sin (x / 2) = 0
  ·
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    have h1 : ∀ k : ℕ, cos ((↑k + 1) * x) = 1 := fun k => by
      have := cos_eq_one_of_sin_half_eq_zero x hsin (k + 1)
      convert this using 1; push_cast; ring
    simp_rw [h1, Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
    rw [sum_odd_eq_sq]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp
  ·
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]


    congr 1


    have hdir : ∀ (j : ℕ), sin ((2 * ↑j + 1) * (x / 2)) * sin (x / 2) =
        sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
      intro j; rw [dirichlet_identity j x]; ring

    have htel := fejer_telescope N x

    have hsum : sin (x / 2) ^ 2 * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) = sin (↑N * x / 2) ^ 2 := by
      rw [Finset.mul_sum]
      have : ∀ i ∈ Finset.range N,
          sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range i, cos ((↑k + 1) * x)) =
          sin ((2 * ↑i + 1) * (x / 2)) * sin (x / 2) :=
        fun i _ => (hdir i).symm
      rw [Finset.sum_congr rfl this]
      exact htel

    have hsin2 : sin (x / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
    rw [div_pow]
    have hsin2_pos : (0 : ℝ) < sin (x / 2) ^ 2 := by positivity
    rw [div_eq_iff (ne_of_gt hsin2_pos)]
    linarith


theorem fejerKernel_isTrigPolynomial (N : ℕ) : IsTrigPolynomial (fejerKernel N) := by
  by_cases hN : N = 0
  ·
    subst hN
    exact ⟨0, fun _ => 0, fun _ => 0, fun x => by simp [fejerKernel]⟩
  ·
    have hkey : ∀ x, fejerKernel N x =
        (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) :=
      fun x => fejerKernel_eq_dirichlet_avg N hN x

    have h_sum_tp : IsTrigPolynomial (fun x =>
        ∑ j ∈ Finset.range N, (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x))) :=
      isTrigPolynomial_finset_sum (fun j _ => dirichlet_isTrigPolynomial j)

    have h_scaled : IsTrigPolynomial (fun x =>
        (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x))) :=
      isTrigPolynomial_smul (1 / (N : ℝ)) h_sum_tp

    obtain ⟨M, a, b, h_eq⟩ := h_scaled
    exact ⟨M, a, b, fun x => by rw [hkey x]; exact h_eq x⟩


lemma fxy_intervalIntegrable (f : ℝ → ℝ) (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) (x : ℝ) :
    IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have h := (hf_any (x + π) (x - π)).comp_sub_left x
  convert h using 1 <;> ring


lemma periodic_integral_shift (g : ℝ → ℝ) (hg : Function.Periodic g (2 * π)) (x : ℝ) :
    ∫ y in (-π)..π, g (x - y) = ∫ y in (-π)..π, g y := by
  have step1 := (integral_comp_sub_left (a := -π) (b := π) g x).symm
  simp only [sub_neg_eq_add] at step1; rw [← step1]
  have step2 := hg.intervalIntegral_add_eq (x - π) (-π)
  rw [show (x - π) + 2 * π = x + π from by ring, show (-π : ℝ) + 2 * π = π from by ring] at step2
  exact step2


set_option maxHeartbeats 800000 in
lemma single_term_convolution (f : ℝ → ℝ) (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) (a b : ℝ) (n : ℕ) (x : ℝ) :
    ∫ y in (-π)..π, f (x - y) * (a * cos (↑n * y) + b * sin (↑n * y)) =
    (a * (∫ t in (-π)..π, f t * cos (↑n * t)) -
     b * (∫ t in (-π)..π, f t * sin (↑n * t))) * cos (↑n * x) +
    (a * (∫ t in (-π)..π, f t * sin (↑n * t)) +
     b * (∫ t in (-π)..π, f t * cos (↑n * t))) * sin (↑n * x) := by
  have hfx := fxy_intervalIntegrable f hf_per hf_intble x
  have hfc : IntervalIntegrable (fun y => f (x - y) * cos (↑n * y)) volume (-π) π :=
    hfx.mul_continuousOn (continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hfs : IntervalIntegrable (fun y => f (x - y) * sin (↑n * y)) volume (-π) π :=
    hfx.mul_continuousOn (continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hfcx : IntervalIntegrable (fun y => f (x - y) * cos (↑n * (x - y))) volume (-π) π :=
    hfx.mul_continuousOn ((continuous_cos.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).continuousOn)
  have hfsx : IntervalIntegrable (fun y => f (x - y) * sin (↑n * (x - y))) volume (-π) π :=
    hfx.mul_continuousOn ((continuous_sin.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).continuousOn)
  simp_rw [show ∀ y, f (x - y) * (a * cos (↑n * y) + b * sin (↑n * y)) =
      a * (f (x - y) * cos (↑n * y)) + b * (f (x - y) * sin (↑n * y)) from fun y => by ring]
  rw [integral_add (hfc.const_mul a) (hfs.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [show ∀ y, f (x - y) * cos (↑n * y) =
      cos (↑n * x) * (f (x - y) * cos (↑n * (x - y))) +
      sin (↑n * x) * (f (x - y) * sin (↑n * (x - y))) from by
    intro y; have h := Real.cos_sub (↑n * x) (↑n * (x - y))
    rw [show ↑n * x - ↑n * (x - y) = ↑n * y from by ring] at h; rw [h]; ring]
  rw [integral_add (hfcx.const_mul _) (hfsx.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [show ∀ y, f (x - y) * sin (↑n * y) =
      sin (↑n * x) * (f (x - y) * cos (↑n * (x - y))) -
      cos (↑n * x) * (f (x - y) * sin (↑n * (x - y))) from by
    intro y; have h := Real.sin_sub (↑n * x) (↑n * (x - y))
    rw [show ↑n * x - ↑n * (x - y) = ↑n * y from by ring] at h; rw [h]; ring]
  rw [integral_sub (hfcx.const_mul _) (hfsx.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hper_c : Function.Periodic (fun t => f t * cos (↑n * t)) (2 * π) := by
    intro t; simp only [Function.Periodic] at hf_per ⊢
    rw [hf_per, show ↑n * (t + 2 * π) = ↑n * t + ↑(n : ℤ) * (2 * π) from by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
  have hper_s : Function.Periodic (fun t => f t * sin (↑n * t)) (2 * π) := by
    intro t; simp only [Function.Periodic] at hf_per ⊢
    rw [hf_per, show ↑n * (t + 2 * π) = ↑n * t + ↑(n : ℤ) * (2 * π) from by push_cast; ring,
        Real.sin_add_int_mul_two_pi]
  rw [periodic_integral_shift _ hper_c x, periodic_integral_shift _ hper_s x]
  ring


set_option maxHeartbeats 1600000 in
theorem fejerMean_isTrigPolynomial (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    IsTrigPolynomial (fejerMean f N) := by
  obtain ⟨M, aK, bK, hK⟩ := fejerKernel_isTrigPolynomial N
  let Cn : ℕ → ℝ := fun n => ∫ t in (-π)..π, f t * cos (↑n * t)
  let Sn : ℕ → ℝ := fun n => ∫ t in (-π)..π, f t * sin (↑n * t)
  refine ⟨M, fun n => (1 / (2 * π)) * (aK n * Cn n - bK n * Sn n),
            fun n => (1 / (2 * π)) * (aK n * Sn n + bK n * Cn n), fun x => ?_⟩
  simp only [fejerMean, periodicConvolution]
  simp_rw [hK]
  simp_rw [Finset.mul_sum]
  have hfx := fxy_intervalIntegrable f hf_per hf_intble x
  have h_intble : ∀ n ∈ Finset.range (M + 1),
      IntervalIntegrable (fun y => f (x - y) * (aK n * cos (↑n * y) + bK n * sin (↑n * y)))
        volume (-π) π := fun n _ =>
    hfx.mul_continuousOn ((((continuous_const.mul (continuous_cos.comp
      (continuous_const.mul continuous_id))).add (continuous_const.mul (continuous_sin.comp
      (continuous_const.mul continuous_id))))).continuousOn)
  rw [intervalIntegral.integral_finset_sum h_intble, Finset.mul_sum]
  congr 1; ext n
  rw [single_term_convolution f hf_per hf_intble (aK n) (bK n) n x]
  ring


theorem intble_diff_abs (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (_hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable (fun x => |f x - g x|) volume (-π) π :=
  (hf.sub (hg_cont.intervalIntegrable (-π) π)).abs

theorem intble_cts_conv (g : ℝ → ℝ) (N : ℕ)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable
      (fun x => |g x - periodicConvolution g (fejerKernel N) x|) volume (-π) π := by

  have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := 2 * π)).exists_bound_of_continuousOn
    hg_cont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_refl _, by linarith⟩)
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    obtain ⟨y, hy_mem, hy_eq⟩ := hg_per.exists_mem_Ico₀ h2pi_pos x
    have h1 : |g y| ≤ M := by
      rw [← Real.norm_eq_abs]; exact hM y (Ico_subset_Icc_self hy_mem)
    rw [hy_eq]; exact h1

  have hKbdd : ∀ y, |fejerKernel N y| ≤ ↑N := fun y => by
    rw [abs_of_nonneg (fejerKernel_nonneg_aux N y)]
    exact fejerKernel_le_N N y

  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hcont_int : Continuous (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) := by
    have heq : (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) =
      (fun x => ∫ y, g (x - y) * fejerKernel N y ∂(volume.restrict (Set.Ioc (-π) π))) := by
      ext x; rw [intervalIntegral.integral_of_le hpi]
    rw [heq]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-π : ℝ) π)) := by
      constructor; rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top
    apply continuous_of_dominated
    · intro x
      exact ((hg_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        (fejerKernel_measurable N).aestronglyMeasurable).restrict
    · intro x
      filter_upwards with y
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgM _) (hKbdd _) (abs_nonneg _) hM0
    · exact integrable_const _
    · filter_upwards with y
      exact (hg_cont.comp (continuous_sub_right y)).mul continuous_const

  have hcont_conv : Continuous (periodicConvolution g (fejerKernel N)) := by
    show Continuous (fun x => (1 / (2 * π)) * ∫ y in (-π)..π, g (x - y) * fejerKernel N y)
    exact continuous_const.mul hcont_int

  exact ((hg_cont.sub hcont_conv).abs).intervalIntegrable (-π) π


lemma periodicConv_intervalIntegrable (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) :
    IntervalIntegrable (periodicConvolution f (fejerKernel N)) volume (-π) π := by

  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have hf_loc : LocallyIntegrable f volume := by
    intro x
    exact ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (hf_any (x - 2) (x + 1)).1.mono_set (fun y hy => ⟨by linarith [hy.1], hy.2⟩)⟩

  have hf_aesm := hf_loc.aestronglyMeasurable
  obtain ⟨g, hg_sm, hfg⟩ := hf_aesm


  have hconv_eq : ∀ x, periodicConvolution f (fejerKernel N) x =
      periodicConvolution g (fejerKernel N) x := by
    intro x
    simp only [periodicConvolution]
    congr 1
    apply intervalIntegral.integral_congr_ae
    have hfg_shift : (fun y => f (x - y)) =ᵐ[volume] (fun y => g (x - y)) :=
      (quasiMeasurePreserving_sub_left volume x).ae_eq hfg
    filter_upwards [hfg_shift] with y hy _
    rw [hy]

  have hconv_sm : StronglyMeasurable (fun x => periodicConvolution g (fejerKernel N) x) := by
    show StronglyMeasurable (fun x => (1 / (2 * π)) * ∫ y in (-π)..π, g (x - y) * fejerKernel N y)
    apply StronglyMeasurable.const_mul
    have hle : (-π : ℝ) ≤ π := by linarith [pi_pos]
    have h1 : (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) =
      (fun x => ∫ y, g (x - y) * fejerKernel N y ∂(volume.restrict (Set.Ioc (-π) π))) := by
      ext x; rw [intervalIntegral.integral_of_le hle]
    rw [h1]
    exact ((hg_sm.comp_measurable (measurable_fst.sub measurable_snd)).mul
      ((fejerKernel_measurable N).stronglyMeasurable.comp_measurable measurable_snd)).integral_prod_right

  have hconv_sm' : StronglyMeasurable (periodicConvolution f (fejerKernel N)) := by
    have : periodicConvolution f (fejerKernel N) = fun x => periodicConvolution g (fejerKernel N) x :=
      funext hconv_eq
    rw [this]; exact hconv_sm

  rw [intervalIntegrable_iff]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]

  have hf_per_norm : Function.Periodic (fun y => ‖f y‖) (2 * π) := by
    intro y; simp only [hf_per y]
  have hf_norm : ∀ x, ∫ y in (-π)..π, ‖f (x - y)‖ = ∫ y in (-π)..π, ‖f y‖ := by
    intro x
    rw [intervalIntegral.integral_comp_sub_left (fun u => ‖f u‖) x]
    conv_lhs => rw [show x - π = -π + x from by ring, show x - -π = -π + x + 2 * π from by ring]
    exact (hf_per_norm.intervalIntegral_add_eq (-π + x) (-π)).trans (by
      rw [show (-π : ℝ) + 2 * π = π from by ring])

  have hC : ∀ x, ‖periodicConvolution f (fejerKernel N) x‖ ≤
      (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖) := by
    intro x
    simp only [periodicConvolution, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity)]
    have h_abs_le : |∫ y in (-π)..π, f (x - y) * fejerKernel N y| ≤
        ∫ y in (-π)..π, ‖f (x - y) * fejerKernel N y‖ := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_integral_norm hpi_le
    calc (1 / (2 * π)) * |∫ y in (-π)..π, f (x - y) * fejerKernel N y|
        ≤ (1 / (2 * π)) * ∫ y in (-π)..π, ‖f (x - y) * fejerKernel N y‖ := by gcongr
      _ ≤ (1 / (2 * π)) * ∫ y in (-π)..π, ‖f (x - y)‖ * ↑N := by
          gcongr
          have h_ub : IntervalIntegrable (fun y => ‖f (x - y)‖ * ↑N) volume (-π) π := by
            have hfx : IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
              have h := (hf_any (x + π) (x - π)).comp_sub_left x
              convert h using 1 <;> ring
            exact hfx.norm.mul_const ↑N

          exact integral_mono_on hpi_le
            (conv_intble_of_periodic f hf_per hf N x).norm h_ub
            (fun y _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (by rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N y)]
                    exact fejerKernel_le_N N y)
                (norm_nonneg _))

      _ = (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f (x - y)‖) := by
          congr 1; rw [← intervalIntegral.integral_const_mul]
          congr 1; ext y; ring
      _ = (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖) := by rw [hf_norm x]
  exact IntegrableOn.of_bound measure_Ioc_lt_top
    hconv_sm'.aestronglyMeasurable.restrict
    ((1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖))
    (Eventually.of_forall (fun x => hC x))

theorem intble_result (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) :
    IntervalIntegrable (fun x => |f x - fejerMean f N x|) volume (-π) π :=
  (hf.sub (periodicConv_intervalIntegrable f N hf_per hf)).abs

theorem intble_conv_diff (f g : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable
      (fun x => |periodicConvolution g (fejerKernel N) x -
                  periodicConvolution f (fejerKernel N) x|) volume (-π) π :=
  ((periodicConv_intervalIntegrable g N hg_per (hg_cont.intervalIntegrable (-π) π)).sub
    (periodicConv_intervalIntegrable f N hf_per hf)).abs

theorem intble_diff (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (_hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable (fun x => g x - f x) volume (-π) π :=
  (hg_cont.intervalIntegrable (-π) π).sub hf

set_option maxHeartbeats 800000 in
theorem fejer_L1_convergence
    (f : ℝ → ℝ)
    (hf_periodic : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    Tendsto (fun N => periodicL1Norm (fun x => f x - fejerMean f N x))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨g, hg_cont, hg_per, hg_approx⟩ :=
    continuous_periodic_dense_L1 f hf_periodic hf_intble (ε / 4) (by linarith)

  obtain ⟨N₀, hN₀⟩ := fejer_uniform_convergence g hg_cont hg_per (ε / 4) (by linarith)
  use N₀
  intro N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (periodicL1Norm_nonneg _)]

  simp only [periodicL1Norm, fejerMean]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]


  have h_pw : ∀ x, |f x - periodicConvolution f (fejerKernel N) x| ≤
      |f x - g x| + |g x - periodicConvolution g (fejerKernel N) x| +
      |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x| := by
    intro x
    have : f x - periodicConvolution f (fejerKernel N) x =
      (f x - g x) + (g x - periodicConvolution g (fejerKernel N) x) +
      (periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x) := by ring
    rw [this]
    calc |(f x - g x) + (g x - periodicConvolution g (fejerKernel N) x) +
          (periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x)|
        ≤ |(f x - g x) + (g x - periodicConvolution g (fejerKernel N) x)| +
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| :=
          abs_add_le _ _
      _ ≤ (|f x - g x| + |g x - periodicConvolution g (fejerKernel N) x|) +
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| := by
          linarith [abs_add_le (f x - g x)
            (g x - periodicConvolution g (fejerKernel N) x)]

  have h_intble_sum :=
    ((intble_diff_abs f g hf_intble hg_cont hg_per).add
      (intble_cts_conv g N hg_cont hg_per)).add
      (intble_conv_diff f g N hf_periodic hf_intble hg_cont hg_per)


  have t1 : (1 / (2 * π)) * ∫ x in (-π)..π, |f x - g x| ≤ ε / 4 := hg_approx

  have t2 : (1 / (2 * π)) * ∫ x in (-π)..π,
      |g x - periodicConvolution g (fejerKernel N) x| ≤ ε / 4 := by
    calc (1 / (2 * π)) * ∫ x in (-π)..π,
          |g x - periodicConvolution g (fejerKernel N) x|
        ≤ (1 / (2 * π)) * ∫ x in (-π)..π, (ε / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact integral_mono_on hpi_le (intble_cts_conv g N hg_cont hg_per)
            _root_.intervalIntegrable_const (fun x _ => hN₀ N hN x)
      _ = ε / 4 := by
          rw [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
          have : π ≠ 0 := ne_of_gt pi_pos; field_simp; ring

  have t3 : (1 / (2 * π)) * ∫ x in (-π)..π,
      |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x| ≤ ε / 4 := by
    have h_eq : (fun x => |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x|) =
        (fun x => |periodicConvolution (fun y => g y - f y) (fejerKernel N) x|) := by
      ext x; rw [convolution_linear g f N x (conv_intble_of_continuous g hg_cont N x)
        (conv_intble_of_periodic f hf_periodic hf_intble N x)]
    rw [h_eq]
    calc periodicL1Norm
          (periodicConvolution (fun y => g y - f y) (fejerKernel N))
        ≤ periodicL1Norm (fun y => g y - f y) :=
          young_fejerKernel _ N (intble_diff f g hf_intble hg_cont hg_per)
            (hg_per.sub hf_periodic)
      _ = periodicL1Norm (fun y => f y - g y) := periodicL1Norm_sub_comm g f
      _ ≤ ε / 4 := hg_approx

  calc (1 / (2 * π)) * ∫ x in (-π)..π,
        |f x - periodicConvolution f (fejerKernel N) x|
      ≤ (1 / (2 * π)) * ∫ x in (-π)..π,
          (|f x - g x| + |g x - periodicConvolution g (fejerKernel N) x| +
            |periodicConvolution g (fejerKernel N) x -
              periodicConvolution f (fejerKernel N) x|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_mono_on hpi_le
          (intble_result f N hf_periodic hf_intble) h_intble_sum
          (fun x _ => h_pw x)
    _ = (1 / (2 * π)) * (∫ x in (-π)..π, |f x - g x|) +
        (1 / (2 * π)) * (∫ x in (-π)..π,
          |g x - periodicConvolution g (fejerKernel N) x|) +
        (1 / (2 * π)) * ∫ x in (-π)..π,
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| := by
        rw [intervalIntegral.integral_add
              ((intble_diff_abs f g hf_intble hg_cont hg_per).add
                (intble_cts_conv g N hg_cont hg_per))
              (intble_conv_diff f g N hf_periodic hf_intble hg_cont hg_per),
            intervalIntegral.integral_add
              (intble_diff_abs f g hf_intble hg_cont hg_per)
              (intble_cts_conv g N hg_cont hg_per)]
        ring
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith

end FejerL1Density

end
