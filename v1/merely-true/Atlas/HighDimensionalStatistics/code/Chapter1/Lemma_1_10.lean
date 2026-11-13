/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped ENNReal NNReal
open MeasureTheory Real Set Measure Filter

/-- Helper geometric tail bound: for `0 ≤ r ≤ 1/2`, the tail series `∑ r^(k+2)` is at
most `2 * r^2`. -/
lemma tsum_geometric_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    ∑' (k : ℕ), r ^ (k + 2) ≤ 2 * r ^ 2 := by
  have hr1 : r < 1 := by linarith
  have hrn : (fun k : ℕ => r ^ (k + 2)) = fun k => r ^ 2 * r ^ k := by
    ext k; ring
  rw [hrn, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [mul_comm 2 (r ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - r) (by positivity)]
  linarith

/-- Moment bound from Lemma 1.10: if `P(|X| > t) ≤ 2 e^(-2t/λ)`, then
`E[|X|^k] ≤ λ^k · k!` for every `k ≥ 1`. -/
theorem lemma_1_10_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {lambda : ℝ} (hlam : 0 < lambda)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (k : ℝ)) ∂μ ≤
      ENNReal.ofReal (lambda ^ k * ↑k.factorial) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)

  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun ω => abs_nonneg _)) hX_meas.aemeasurable.norm hk_pos]

  have hstep2 : ∫⁻ t in Ioi (0 : ℝ),
      μ {a | t < |X a|} * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * exp (-2 * t / lambda)) *
          ENNReal.ofReal (t ^ ((k : ℝ) - 1)) := by
    apply lintegral_mono; intro t
    show μ {a | t < |X a|} * _ ≤ ENNReal.ofReal _ * _
    gcongr
    by_cases ht : 0 < t
    · exact hX_tail t ht
    · push Not at ht
      calc μ {a | t < |X a|}
          ≤ (μ : Measure Ω) univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (2 * exp (-2 * t / lambda)) := by
            rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
            linarith [add_one_le_exp (-2 * t / lambda),
                      div_nonneg (show (0:ℝ) ≤ -2 * t by linarith) (le_of_lt hlam)]

  have hstep3 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * exp (-2 * t / lambda)) *
        ENNReal.ofReal (t ^ ((k : ℝ) - 1)) =
      ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1)) := by
    congr 1; ext t; rw [← ENNReal.ofReal_mul (by positivity)]

  have hs_int : (-1 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hint_on := integrableOn_rpow_mul_exp_neg_mul_rpow hs_int le_rfl
    (show (0:ℝ) < 2 / lambda by positivity)
  have hintble : IntegrableOn
      (fun t : ℝ => 2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1))
      (Ioi 0) volume := by
    apply Integrable.congr (hint_on.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [rpow_one, mem_Ioi] at *; ring_nf
  have hstep4 : ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1)) =
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ),
        2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1)) := by
    symm; apply ofReal_integral_eq_lintegral_ofReal hintble
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    exact mul_nonneg (mul_nonneg (by norm_num) (exp_nonneg _)) (rpow_nonneg (le_of_lt ht) _)

  calc ENNReal.ofReal (k : ℝ) *
      ∫⁻ t in Ioi 0, μ {a | t < |X a|} * ENNReal.ofReal (t ^ ((k : ℝ) - 1))
    ≤ ENNReal.ofReal (k : ℝ) *
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ),
        2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1)) := by
        gcongr; exact le_trans hstep2 (le_of_eq (hstep3.trans hstep4))
    _ = ENNReal.ofReal ((k : ℝ) * ∫ t in Ioi (0 : ℝ),
        2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (lambda ^ k * ↑k.factorial) := by
        apply ENNReal.ofReal_le_ofReal

        have h2l_pos : (0 : ℝ) < 2 / lambda := by positivity
        have hrewrite : ∫ t in Ioi (0 : ℝ),
            2 * exp (-2 * t / lambda) * t ^ ((k : ℝ) - 1) =
            2 * ∫ t in Ioi (0 : ℝ),
              t ^ ((k : ℝ) - 1) * rexp (-(2 / lambda * t)) := by
          rw [show (2 : ℝ) = ((2 : ℝ) : ℝ) from rfl, ← smul_eq_mul, ← integral_smul]
          congr 1; ext t; simp only [smul_eq_mul]; ring_nf
        rw [hrewrite]
        have hint : ∫ t in Ioi (0 : ℝ),
            t ^ ((k : ℝ) - 1) * rexp (-(2 / lambda * t)) =
            (1 / (2 / lambda)) ^ (k : ℝ) * Gamma (k : ℝ) :=
          Real.integral_rpow_mul_exp_neg_mul_Ioi hk_pos h2l_pos
        rw [hint, show (1 : ℝ) / (2 / lambda) = lambda / 2 from by field_simp]
        have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have hk_Gamma : (k : ℝ) * Gamma (k : ℝ) = ↑k.factorial := by
          rw [← Real.Gamma_nat_eq_factorial k, Real.Gamma_add_one hk0, mul_comm]
        calc (k : ℝ) * (2 * ((lambda / 2) ^ (k : ℝ) * Gamma (k : ℝ)))
            = 2 * (lambda / 2) ^ (k : ℝ) * ((k : ℝ) * Gamma (k : ℝ)) := by ring
          _ = 2 * (lambda / 2) ^ (k : ℝ) * ↑k.factorial := by rw [hk_Gamma]
          _ ≤ lambda ^ (k : ℝ) * ↑k.factorial := by
              gcongr
              rw [Real.rpow_natCast, Real.rpow_natCast]
              calc 2 * (lambda / 2) ^ k
                  = 2 * (lambda ^ k / 2 ^ k) := by rw [div_pow]
                _ ≤ 2 * (lambda ^ k / 2) := by
                    gcongr; exact le_self_pow₀ one_le_two (by omega)
                _ = lambda ^ k := by ring
          _ = lambda ^ k * ↑k.factorial := by rw [Real.rpow_natCast]

/-- Corollary of Lemma 1.10: taking `k`-th roots of the moment bound `E ≤ λ^k · k!`
yields `E^{1/k} ≤ 2 λ k`, using the elementary inequality `k! ≤ k^k`. -/
theorem lemma_1_10_moment_root_bound (l : ℝ) (hl : 0 < l) (k : ℕ) (hk : 1 ≤ k)
    (E : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ l ^ k * ↑k.factorial) :
    E ^ ((k : ℝ)⁻¹) ≤ 2 * l * ↑k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by positivity
  have hfact_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hE_le_lk : E ≤ (l * k) ^ k := by
    calc E ≤ l ^ k * ↑k.factorial := hE
      _ ≤ l ^ k * (k : ℝ) ^ k := by gcongr
      _ = (l * k) ^ k := by rw [mul_pow]
  have hlk_pos : (0 : ℝ) ≤ l * k := by positivity
  calc E ^ ((k : ℝ)⁻¹) ≤ ((l * k) ^ k) ^ ((k : ℝ)⁻¹) := by
        apply Real.rpow_le_rpow hE0 hE_le_lk
        exact inv_nonneg.mpr (le_of_lt hk0)
      _ = l * k := by
          rw [← Real.rpow_natCast (l * k) k, ← Real.rpow_mul hlk_pos]
          simp [Nat.cast_ne_zero.mpr (by omega : k ≠ 0)]
      _ ≤ 2 * l * k := by nlinarith

/-- Term-by-term Taylor/DCT expansion of the MGF: under the tail hypothesis of
Lemma 1.10 (and `E[X] = 0`), for `0 < s ≤ 1/(2λ)`,
`E[e^{sX}] ≤ 1 + ∑_{k ≥ 0} (sλ)^{k+2}`. -/
theorem mgf_taylor_dct_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} {lambda s : ℝ}
    (hX_meas : AEStronglyMeasurable X μ)
    (lambda_pos : 0 < lambda)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)))
    (hX_centered : ∫ ω, X ω ∂μ = 0)
    (s_pos : 0 < s) (s_le : s ≤ 1 / (2 * lambda)) :
    ∫ (ω : Ω), Real.exp (s * X ω) ∂μ ≤
      1 + ∑' (k : ℕ), (s * lambda) ^ (k + 2) := by

  have hsl : s * lambda ≤ 1 / 2 := by
    calc s * lambda ≤ 1 / (2 * lambda) * lambda :=
          mul_le_mul_of_nonneg_right s_le (le_of_lt lambda_pos)
      _ = 1 / 2 := by field_simp
  have hsl_pos : 0 ≤ s * lambda := by positivity
  have hsl_lt_one : s * lambda < 1 := by linarith

  have moment_bound_nat : ∀ k : ℕ, 1 ≤ k →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ ≤
        ENNReal.ofReal (lambda ^ k * ↑k.factorial) := by
    intro k hk
    have h := lemma_1_10_moment_bound lambda_pos hX_meas hX_tail k hk
    simp_rw [rpow_natCast] at h
    exact h

  have int_abs_bound : ∀ k : ℕ, 1 ≤ k →
      Integrable (fun ω => |X ω| ^ k) μ ∧
      ∫ ω, |X ω| ^ k ∂μ ≤ lambda ^ k * ↑k.factorial := by
    intro k hk
    have h_int : Integrable (fun ω => |X ω| ^ k) μ := ⟨hX_meas.norm.pow k, by
      calc ∫⁻ ω, ‖|X ω| ^ k‖ₑ ∂μ
          = ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ := by
            congr 1; ext ω
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        _ ≤ ENNReal.ofReal (lambda ^ k * ↑k.factorial) := moment_bound_nat k hk
        _ < ⊤ := ENNReal.ofReal_lt_top⟩
    refine ⟨h_int, ?_⟩
    have h_ofReal : ENNReal.ofReal (∫ ω, |X ω| ^ k ∂μ) ≤
        ENNReal.ofReal (lambda ^ k * ↑k.factorial) := by
      rw [ofReal_integral_eq_lintegral_ofReal h_int
          (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _))]
      exact moment_bound_nat k hk
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h_ofReal

  let F : ℕ → Ω → ℝ := fun k ω => (s * X ω) ^ k / (k.factorial : ℝ)

  have hF_meas : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    exact ((hX_meas.const_mul s).pow k).const_smul ((k.factorial : ℝ)⁻¹) |>.congr (by
      filter_upwards with ω
      simp [F, div_eq_mul_inv, Pi.smul_apply, smul_eq_mul, mul_comm])

  have h_enorm_ne_top : ∑' k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≠ ⊤ := by
    have h_bound : ∀ k, ∫⁻ ω, ‖F k ω‖ₑ ∂μ ≤ ENNReal.ofReal ((s * lambda) ^ k) := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · simp [F, enorm_one]
      · show ∫⁻ ω, ‖(s * X ω) ^ k / (↑k.factorial : ℝ)‖ₑ ∂μ ≤ _
        have h1 : ∀ ω, ‖(s * X ω) ^ k / (↑k.factorial : ℝ)‖ₑ =
            ENNReal.ofReal (s ^ k / ↑k.factorial) * ENNReal.ofReal (|X ω| ^ k) := by
          intro ω
          rw [Real.enorm_eq_ofReal_abs, abs_div, abs_pow, abs_mul, abs_of_pos s_pos, Nat.abs_cast,
              ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        simp_rw [h1]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (s ^ k / ↑k.factorial) *
              ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ
            ≤ ENNReal.ofReal (s ^ k / ↑k.factorial) *
              ENNReal.ofReal (lambda ^ k * ↑k.factorial) := by
              gcongr; exact moment_bound_nat k hk_pos
          _ = ENNReal.ofReal ((s * lambda) ^ k) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1; rw [mul_pow]; field_simp
    exact ne_top_of_le_ne_top
      (summable_geometric_of_lt_one hsl_pos hsl_lt_one).tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum h_bound)

  have h_exp_eq : ∀ ω, Real.exp (s * X ω) = ∑' k, F k ω := by
    intro ω
    show Real.exp (s * X ω) = ∑' k, (s * X ω) ^ k / (k.factorial : ℝ)
    rw [Real.exp_eq_exp_ℝ]
    exact congr_fun NormedSpace.exp_eq_tsum_div (s * X ω)

  have h_interchange : ∫ ω, (∑' k, F k ω) ∂μ = ∑' k, ∫ ω, F k ω ∂μ :=
    integral_tsum hF_meas h_enorm_ne_top

  have h_int_F : ∀ k, ∫ ω, F k ω ∂μ = s ^ k / ↑k.factorial * ∫ ω, (X ω) ^ k ∂μ := by
    intro k
    show ∫ ω, (s * X ω) ^ k / (↑k.factorial : ℝ) ∂μ = _
    simp_rw [mul_pow, mul_div_assoc]
    rw [integral_const_mul, integral_div]
    ring

  set a := fun k : ℕ => s ^ k / ↑k.factorial * ∫ ω, (X ω) ^ k ∂μ with ha_def
  have h_summable : Summable a := by
    apply Summable.of_norm_bounded (g := fun k => (s * lambda) ^ k)
      (summable_geometric_of_lt_one hsl_pos hsl_lt_one)
    intro k
    by_cases hk : k = 0
    · subst hk; simp [ha_def, integral_const]
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simp only [ha_def, norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos s_pos, Nat.abs_cast]
      calc s ^ k / ↑k.factorial * |∫ ω, (X ω) ^ k ∂μ|
          ≤ s ^ k / ↑k.factorial * (lambda ^ k * ↑k.factorial) := by
            gcongr
            calc |∫ ω, (X ω) ^ k ∂μ|
                = ‖∫ ω, (X ω) ^ k ∂μ‖ := (Real.norm_eq_abs _).symm
              _ ≤ ∫ ω, ‖(X ω) ^ k‖ ∂μ := norm_integral_le_integral_norm _
              _ = ∫ ω, |X ω| ^ k ∂μ := by congr 1; ext ω; rw [Real.norm_eq_abs, abs_pow]
              _ ≤ lambda ^ k * ↑k.factorial := (int_abs_bound k hk_pos).2
        _ = (s * lambda) ^ k := by rw [mul_pow]; field_simp

  have h_eq_tsum : ∫ ω, Real.exp (s * X ω) ∂μ = ∑' k, a k := by
    calc ∫ ω, Real.exp (s * X ω) ∂μ
        = ∫ ω, (∑' k, F k ω) ∂μ := by congr 1; ext ω; exact h_exp_eq ω
      _ = ∑' k, ∫ ω, F k ω ∂μ := h_interchange
      _ = ∑' k, a k := by congr 1; ext k; exact h_int_F k

  have ha0 : a 0 = 1 := by simp [ha_def, integral_const, Measure.real, measure_univ]

  have ha1 : a 1 = 0 := by simp [ha_def, hX_centered]

  have h_split : ∑' k, a k = 1 + ∑' k, a (k + 2) := by
    rw [h_summable.tsum_eq_zero_add, ha0]
    congr 1
    have ha' : Summable (fun k => a (k + 1)) := h_summable.comp_injective (fun a b h => by omega)
    rw [ha'.tsum_eq_zero_add, ha1, zero_add]

  have h_bound : ∀ k, a (k + 2) ≤ (s * lambda) ^ (k + 2) := by
    intro k
    show s ^ (k + 2) / ↑(k + 2).factorial * ∫ ω, (X ω) ^ (k + 2) ∂μ ≤ (s * lambda) ^ (k + 2)
    have hk2 : 1 ≤ k + 2 := by omega
    have h_int_bound : ∫ ω, (X ω) ^ (k + 2) ∂μ ≤ lambda ^ (k + 2) * ↑(k + 2).factorial := by
      obtain ⟨h_int_abs, h_abs_le⟩ := int_abs_bound (k + 2) hk2
      have h_Xk_int : Integrable (fun ω => (X ω) ^ (k + 2)) μ := ⟨hX_meas.pow (k + 2), by
        calc ∫⁻ ω, ‖(X ω) ^ (k + 2)‖ₑ ∂μ
            = ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (k + 2)) ∂μ := by
              congr 1; ext ω; rw [Real.enorm_eq_ofReal_abs, abs_pow]
          _ ≤ ENNReal.ofReal (lambda ^ (k + 2) * ↑(k + 2).factorial) :=
              moment_bound_nat (k + 2) hk2
          _ < ⊤ := ENNReal.ofReal_lt_top⟩
      calc ∫ ω, (X ω) ^ (k + 2) ∂μ
          ≤ ∫ ω, |X ω| ^ (k + 2) ∂μ := by
            apply integral_mono h_Xk_int h_int_abs
            intro ω
            calc (X ω) ^ (k + 2) ≤ |(X ω) ^ (k + 2)| := le_abs_self _
              _ = |X ω| ^ (k + 2) := abs_pow (X ω) (k + 2)
        _ ≤ lambda ^ (k + 2) * ↑(k + 2).factorial := h_abs_le
    calc s ^ (k + 2) / ↑(k + 2).factorial * ∫ ω, (X ω) ^ (k + 2) ∂μ
        ≤ s ^ (k + 2) / ↑(k + 2).factorial * (lambda ^ (k + 2) * ↑(k + 2).factorial) := by
          apply mul_le_mul_of_nonneg_left h_int_bound (by positivity)
      _ = (s * lambda) ^ (k + 2) := by rw [mul_pow]; field_simp

  rw [h_eq_tsum, h_split]
  have ha' : Summable (fun k => a (k + 1)) := h_summable.comp_injective (fun a b h => by omega)
  have h_sum_shifted : Summable (fun k => a (k + 2)) :=
    ha'.comp_injective (fun a b h => by omega)
  have h_sum_geom : Summable (fun k : ℕ => (s * lambda) ^ (k + 2)) :=
    (summable_geometric_of_lt_one hsl_pos hsl_lt_one).comp_injective (fun a b h => by omega)
  linarith [Summable.tsum_mono h_sum_shifted h_sum_geom h_bound]

/-- One-sided MGF bound from Lemma 1.10: for `0 < s ≤ 1/(2λ)`,
`E[e^{sX}] ≤ exp(2 s^2 λ^2)`. -/
theorem mgf_bound_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {lambda : ℝ} (hlam : 0 < lambda)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)))
    (hX_centered : ∫ ω, X ω ∂μ = 0)
    (s : ℝ) (hs_pos : 0 < s) (s_le : s ≤ 1 / (2 * lambda)) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (2 * s ^ 2 * lambda ^ 2) := by
  have hR := mgf_taylor_dct_bound hX_meas hlam hX_tail hX_centered hs_pos s_le
  have hslam : s * lambda ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right s_le (le_of_lt hlam)
    have : 1 / (2 * lambda) * lambda = 1 / 2 := by field_simp
    linarith
  have hsl0 : 0 ≤ s * lambda := by positivity
  calc ∫ ω, Real.exp (s * X ω) ∂μ
      ≤ 1 + ∑' (k : ℕ), (s * lambda) ^ (k + 2) := hR
    _ ≤ 1 + 2 * (s * lambda) ^ 2 := by linarith [tsum_geometric_tail_le hsl0 hslam]
    _ = 1 + 2 * s ^ 2 * lambda ^ 2 := by ring
    _ ≤ Real.exp (2 * s ^ 2 * lambda ^ 2) := by
        linarith [add_one_le_exp (2 * s ^ 2 * lambda ^ 2)]

/-- Two-sided MGF bound from Lemma 1.10: for any `s` with `|s| ≤ 1/(2λ)`,
`E[e^{sX}] ≤ exp(2 s^2 λ^2)`. -/
theorem lemma_1_10_mgf_bound_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {lambda : ℝ} (hlam : 0 < lambda)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)))
    (hX_centered : ∫ ω, X ω ∂μ = 0)
    (s : ℝ) (hs : |s| ≤ 1 / (2 * lambda)) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (2 * s ^ 2 * lambda ^ 2) := by
  rcases lt_trichotomy s 0 with hs_neg | hs_zero | hs_pos
  ·
    have hs' : 0 < -s := neg_pos.mpr hs_neg
    have hs_le' : -s ≤ 1 / (2 * lambda) := by rwa [abs_of_neg hs_neg] at hs
    have heq : ∀ ω, Real.exp (s * X ω) = Real.exp ((-s) * (-X) ω) := by
      intro ω; simp
    simp_rw [heq]
    have hX_tail' : ∀ t : ℝ, 0 < t →
        μ {ω | |(-X) ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)) := by
      intro t ht; simp only [Pi.neg_apply, abs_neg]; exact hX_tail t ht
    have hX_centered' : ∫ ω, (-X) ω ∂μ = 0 := by simp [integral_neg, hX_centered]
    have hX_meas' : AEStronglyMeasurable (-X) μ := hX_meas.neg
    have h := mgf_bound_pos hlam hX_meas' hX_tail' hX_centered' (-s) hs' hs_le'
    convert h using 2; ring
  ·
    subst hs_zero; simp [integral_const]
  ·
    exact mgf_bound_pos hlam hX_meas hX_tail hX_centered s hs_pos
      (by rwa [abs_of_pos hs_pos] at hs)

/-- Lemma 1.10 (combined form). Assume `X` is centered and satisfies
`P(|X| > t) ≤ 2 e^(-2t/λ)`. Then:
1. `E[|X|^k] ≤ λ^k · k!` for every `k ≥ 1`.
2. Any nonnegative `E ≤ λ^k · k!` satisfies `E^{1/k} ≤ 2 λ k`.
3. The MGF is bounded: for `|s| ≤ 1/(2λ)`, `E[e^{sX}] ≤ exp(2 s^2 λ^2)`. -/
theorem lemma_1_10
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {lambda : ℝ} (hlam : 0 < lambda)
    (hX_meas : AEStronglyMeasurable X μ)
    (hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t / lambda)))
    (hX_centered : ∫ ω, X ω ∂μ = 0) :

    (∀ (k : ℕ), 1 ≤ k →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (k : ℝ)) ∂μ ≤
        ENNReal.ofReal (lambda ^ k * ↑k.factorial)) ∧

    (∀ (k : ℕ), 1 ≤ k →
      ∀ (E_val : ℝ), 0 ≤ E_val → E_val ≤ lambda ^ k * ↑k.factorial →
        E_val ^ ((k : ℝ)⁻¹) ≤ 2 * lambda * ↑k) ∧

    (∀ (s : ℝ), |s| ≤ 1 / (2 * lambda) →
      ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (2 * s ^ 2 * lambda ^ 2)) := by
  exact ⟨
    fun k hk => lemma_1_10_moment_bound hlam hX_meas hX_tail k hk,
    fun k hk E_val hE0 hE => lemma_1_10_moment_root_bound lambda hlam k hk E_val hE0 hE,
    fun s hs => lemma_1_10_mgf_bound_integral hlam hX_meas hX_tail hX_centered s hs⟩
