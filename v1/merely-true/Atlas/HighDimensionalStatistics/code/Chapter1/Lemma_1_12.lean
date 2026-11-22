/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_4
import Mathlib.Analysis.Convex.Integral

set_option maxHeartbeats 1600000

open MeasureTheory Real Finset

/-- Elementary inequality `x² ≤ e^x + e^{-x}`. -/
lemma sq_le_exp_add_exp_neg (x : ℝ) : x ^ 2 ≤ rexp x + rexp (-x) := by
  have hab : rexp x + rexp (-x) = rexp |x| + rexp (-|x|) := by
    cases le_or_gt 0 x with
    | inl hx => rw [abs_of_nonneg hx]
    | inr hx => rw [abs_of_neg hx]; ring_nf
  rw [hab, (sq_abs x).symm]
  have habs : 0 ≤ |x| := abs_nonneg x
  have h4 := Real.sum_le_exp_of_nonneg habs 4
  have hsum : ∑ i ∈ range 4, |x| ^ i / ↑i.factorial =
    1 + |x| + |x| ^ 2 / 2 + |x| ^ 3 / 6 := by
    simp only [sum_range_succ, sum_range_zero, zero_add,
      Nat.factorial, pow_zero, pow_one, Nat.cast_one, div_one]
    push_cast; ring
  rw [hsum] at h4
  nlinarith [exp_pos (-|x|), sq_nonneg (|x| - 3/2), mul_nonneg habs (sq_nonneg (|x| - 3/2))]

/-- If all exponential moments of `X` are integrable, then `X²` is integrable. -/
lemma sq_integrable_of_exp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ}
    (hX_int : Integrable X μ)
    (hX_exp : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ) :
    Integrable (fun ω => X ω ^ 2) μ := by
  have h1 := hX_exp 1; simp only [one_mul] at h1
  have h2 := hX_exp (-1); simp only [neg_one_mul] at h2
  refine (h1.add h2).mono (hX_int.aestronglyMeasurable.pow 2) ?_
  filter_upwards with ω
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (by linarith [exp_pos (X ω), exp_pos (-X ω)])]
  exact sq_le_exp_add_exp_neg (X ω)

/-- `e^x ≤ 1 + x + ∑_{k≥2} |x|^k / k!`: the linear part plus the absolute value of the
Taylor tail dominates the exponential. -/
lemma exp_le_one_add_abs_series (x : ℝ) :
    Real.exp x ≤ 1 + x + ∑' (k : ℕ), |x| ^ (k + 2) / ↑(k + 2).factorial := by

  have hexp : HasSum (fun n : ℕ => x ^ n / ↑(Nat.factorial n)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

  have htail : HasSum (fun k : ℕ => x ^ (k + 2) / ↑((k + 2).factorial))
      (Real.exp x - (1 + x)) := by
    have hpartial : ∑ i ∈ range 2, x ^ i / ↑(i.factorial) = 1 + x := by
      simp [sum_range_succ, Nat.factorial, pow_zero, pow_one]
    rw [← hpartial]; exact (hasSum_nat_add_iff' 2).mpr hexp

  have hexp_abs : HasSum (fun n : ℕ => |x| ^ n / ↑(Nat.factorial n)) (Real.exp |x|) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |x|
  have htail_abs : HasSum (fun k : ℕ => |x| ^ (k + 2) / ↑((k + 2).factorial))
      (Real.exp |x| - (1 + |x|)) := by
    have hpartial : ∑ i ∈ range 2, |x| ^ i / ↑(i.factorial) = 1 + |x| := by
      simp [sum_range_succ, Nat.factorial, pow_zero, pow_one]
    rw [← hpartial]; exact (hasSum_nat_add_iff' 2).mpr hexp_abs

  have hexp_eq : Real.exp x = 1 + x + ∑' k, x ^ (k + 2) / ↑((k + 2).factorial) := by
    linarith [htail.tsum_eq]
  rw [hexp_eq]

  gcongr 1 + x + ?_
  exact Summable.tsum_le_tsum
    (fun k => by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc x ^ (k + 2) ≤ |x ^ (k + 2)| := le_abs_self _
        _ = |x| ^ (k + 2) := abs_pow x (k + 2))
    htail.summable
    htail_abs.summable

/-- DCT-style interchange used in the proof of Lemma 1.12: for centred `Z` with
integrable `e^Z` and `e^{|Z|}`, the MGF is bounded by `1` plus the integrated
tail-series of `|Z|`. -/
lemma dct_interchange_exp_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ}
    (hZ_int : Integrable Z μ)
    (hZ_mean : ∫ ω, Z ω ∂μ = 0)
    (hZ_exp : Integrable (fun ω => rexp (Z ω)) μ)
    (hZ_abs_exp : Integrable (fun ω => rexp (|Z ω|)) μ) :
    ∫ ω, rexp (Z ω) ∂μ
      ≤ 1 + ∑' (k : ℕ), ∫ ω, |Z ω| ^ (k + 2) / ↑(k + 2).factorial ∂μ := by

  set T : Ω → ℝ := fun ω => ∑' (k : ℕ), |Z ω| ^ (k + 2) / ↑(k + 2).factorial with hT_def

  have hT_le_exp : ∀ ω, T ω ≤ rexp (|Z ω|) := by
    intro ω

    have hexp_abs : HasSum (fun n : ℕ => |Z ω| ^ n / ↑(Nat.factorial n)) (Real.exp |Z ω|) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |Z ω|
    have htail_abs : HasSum (fun k : ℕ => |Z ω| ^ (k + 2) / ↑((k + 2).factorial))
        (Real.exp |Z ω| - (1 + |Z ω|)) := by
      have hpartial : ∑ i ∈ range 2, |Z ω| ^ i / ↑(i.factorial) = 1 + |Z ω| := by
        simp [sum_range_succ, Nat.factorial, pow_zero, pow_one]
      rw [← hpartial]; exact (hasSum_nat_add_iff' 2).mpr hexp_abs
    have := htail_abs.tsum_eq
    linarith [abs_nonneg (Z ω), Real.add_one_le_exp (|Z ω|)]
  have hT_nn : ∀ ω, 0 ≤ T ω := fun ω => tsum_nonneg (fun k => by positivity)

  have hT_eq : ∀ ω, T ω = rexp (|Z ω|) - 1 - |Z ω| := by
    intro ω
    have hexp_abs : HasSum (fun n : ℕ => |Z ω| ^ n / ↑(Nat.factorial n)) (Real.exp |Z ω|) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |Z ω|
    have htail_abs : HasSum (fun k : ℕ => |Z ω| ^ (k + 2) / ↑((k + 2).factorial))
        (Real.exp |Z ω| - (1 + |Z ω|)) := by
      have hpartial : ∑ i ∈ range 2, |Z ω| ^ i / ↑(i.factorial) = 1 + |Z ω| := by
        simp [sum_range_succ, Nat.factorial, pow_zero, pow_one]
      rw [← hpartial]; exact (hasSum_nat_add_iff' 2).mpr hexp_abs
    have := htail_abs.tsum_eq; linarith

  have hT_int : Integrable T μ := by
    have hT_eq_fn : T = fun ω => rexp (|Z ω|) - 1 - |Z ω| := by ext ω; exact hT_eq ω
    rw [hT_eq_fn]
    exact (hZ_abs_exp.sub (integrable_const 1)).sub (hZ_int.norm)


  have h_bound_int : Integrable (fun ω => 1 + Z ω + T ω) μ :=
    ((integrable_const 1).add hZ_int).add hT_int

  have h_mono : ∫ ω, rexp (Z ω) ∂μ ≤ ∫ ω, (1 + Z ω + T ω) ∂μ :=
    integral_mono hZ_exp h_bound_int (fun ω => exp_le_one_add_abs_series (Z ω))

  have h_int_1Z : ∫ ω, (1 + Z ω) ∂μ = 1 := by
    have : ∫ ω, (1 : ℝ) ∂μ + ∫ ω, Z ω ∂μ = 1 + 0 := by
      rw [hZ_mean, integral_const]
      simp [Measure.real, IsProbabilityMeasure.measure_univ]
    linarith [integral_add (integrable_const (1 : ℝ)) hZ_int]
  have h_int_eq : ∫ ω, (1 + Z ω + T ω) ∂μ = 1 + ∫ ω, T ω ∂μ := by
    have h1 : ∫ ω, (1 + Z ω + T ω) ∂μ = ∫ ω, (1 + Z ω) ∂μ + ∫ ω, T ω ∂μ :=
      integral_add ((integrable_const 1).add hZ_int) hT_int

    rw [h1, h_int_1Z]


  have h_int_tsum : ∫ ω, T ω ∂μ = ∑' k, ∫ ω, |Z ω| ^ (k + 2) / ↑(k + 2).factorial ∂μ := by


    have h_aesm : ∀ k : ℕ, AEStronglyMeasurable
        (fun ω => |Z ω| ^ (k + 2) / ↑(k + 2).factorial) μ :=
      fun k => (hZ_int.aestronglyMeasurable.norm.pow (k + 2)).smul_const _


    have h_abs_conv : ∑' k, ∫⁻ ω, ‖|Z ω| ^ (k + 2) / ↑(k + 2).factorial‖ₑ ∂μ ≠ ⊤ := by
      have hT_lt_top : ∫⁻ (a : Ω), ‖T a‖ₑ ∂μ < ⊤ :=
        (hasFiniteIntegral_def T μ).mp hT_int.hasFiniteIntegral
      have h_tail_summable : ∀ ω : Ω, Summable (fun k : ℕ => |Z ω| ^ (k + 2) / ↑(k + 2).factorial) := by
        intro ω
        have hexp_abs : HasSum (fun n : ℕ => |Z ω| ^ n / ↑(Nat.factorial n)) (Real.exp |Z ω|) := by
          rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp |Z ω|
        have htail_abs : HasSum (fun k : ℕ => |Z ω| ^ (k + 2) / ↑((k + 2).factorial))
            (Real.exp |Z ω| - (1 + |Z ω|)) := by
          have hpartial : ∑ i ∈ range 2, |Z ω| ^ i / ↑(i.factorial) = 1 + |Z ω| := by
            simp [sum_range_succ, Nat.factorial, pow_zero, pow_one]
          rw [← hpartial]; exact (hasSum_nat_add_iff' 2).mpr hexp_abs
        exact htail_abs.summable
      apply ne_top_of_le_ne_top hT_lt_top.ne
      calc ∑' k, ∫⁻ ω, ‖|Z ω| ^ (k + 2) / ↑(k + 2).factorial‖ₑ ∂μ
          = ∫⁻ ω, ∑' k, ‖|Z ω| ^ (k + 2) / ↑(k + 2).factorial‖ₑ ∂μ :=
            (lintegral_tsum (fun k => (h_aesm k).enorm)).symm
        _ ≤ ∫⁻ ω, ‖T ω‖ₑ ∂μ := by
            apply MeasureTheory.lintegral_mono
            intro ω
            show ∑' k, ‖|Z ω| ^ (k + 2) / ↑(k + 2).factorial‖ₑ ≤ ‖T ω‖ₑ
            have h1 : ∑' k, ‖|Z ω| ^ (k + 2) / ↑(k + 2).factorial‖ₑ =
                ∑' k, ENNReal.ofReal (|Z ω| ^ (k + 2) / ↑(k + 2).factorial) := by
              congr 1; ext k; rw [enorm_eq_ofReal (by positivity)]
            have h2 : ∑' k, ENNReal.ofReal (|Z ω| ^ (k + 2) / ↑(k + 2).factorial) =
                ENNReal.ofReal (T ω) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (h_tail_summable ω)).symm
            rw [h1, h2, enorm_eq_ofReal (hT_nn ω)]

    exact integral_tsum h_aesm h_abs_conv
  linarith [h_mono, h_int_eq, h_int_tsum]

/-- Even moments of a sub-Gaussian random variable: for `X ~ subG(σ²)`,
`E[X^{2k}] ≤ 2 · (2σ²)^k · k!`. -/
theorem subgaussian_even_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq)
    (hX_int : Integrable X μ)
    (hX_mean : ∫ ω, X ω ∂μ = 0)
    (hX_exp : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hX_mgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, (X ω) ^ (2 * k) ∂μ ≤ 2 * (2 * σsq) ^ k * ↑(Nat.factorial k) := by

  have hSG : IsSubGaussian X σsq μ := ⟨hX_int, hX_mean, hX_exp, hX_mgf⟩
  have hX_meas : AEStronglyMeasurable X μ := hX_int.aestronglyMeasurable
  have hX_tail : ∀ t : ℝ, 0 < t →
      μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * rexp (-t ^ 2 / (2 * σsq))) := by
    intro t ht
    have h_upper := lemma_1_3_upper_tail hSG t ht
    have h_lower := lemma_1_3_lower_tail hSG t ht
    have h_subset : {ω | |X ω| > t} ⊆ {ω | X ω > t} ∪ {ω | X ω < -t} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at *
      rcases le_or_gt (X ω) 0 with h | h
      · right; linarith [abs_of_nonpos h ▸ hω]
      · left; linarith [abs_of_pos h ▸ hω]
    calc μ {ω | |X ω| > t}
        ≤ μ ({ω | X ω > t} ∪ {ω | X ω < -t}) := measure_mono h_subset
      _ ≤ μ {ω | X ω > t} + μ {ω | X ω < -t} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (rexp (-(t ^ 2 / (2 * σsq)))) +
          ENNReal.ofReal (rexp (-(t ^ 2 / (2 * σsq)))) := add_le_add h_upper h_lower
      _ = ENNReal.ofReal (2 * rexp (-(t ^ 2 / (2 * σsq)))) := by
          rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]; ring_nf
      _ = ENNReal.ofReal (2 * rexp (-t ^ 2 / (2 * σsq))) := by ring_nf

  have h2k : 1 ≤ 2 * k := by omega
  have h_lem14 := lemma_1_4_moment_bound hσ hX_meas hX_tail (2 * k) h2k

  have h_rhs_eq : (2 * σsq) ^ ((2 * k : ℝ) / 2) * (2 * ↑k) * Gamma ((2 * ↑k) / 2) =
      2 * (2 * σsq) ^ k * ↑(Nat.factorial k) := by
    have hk2_simp : (2 * (k : ℝ)) / 2 = (k : ℝ) := by ring
    rw [hk2_simp]
    rw [rpow_natCast]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [show (↑(j + 1) : ℝ) = ↑j + 1 from by push_cast; ring]
    rw [Gamma_nat_eq_factorial j]
    simp [Nat.factorial_succ]; ring
  rw [show (↑(2 * k) : ℝ) = 2 * ↑k from by push_cast; ring] at h_lem14
  rw [h_rhs_eq] at h_lem14

  have h_rpow_eq : (fun ω => |X ω| ^ (2 * k : ℝ)) = (fun ω => (X ω) ^ (2 * k) : Ω → ℝ) := by
    ext ω
    rw [show (2 * k : ℝ) = ↑(2 * k) from by push_cast; ring, rpow_natCast]
    rw [show 2 * k = k + k from by omega]
    exact Even.pow_abs ⟨k, rfl⟩ (X ω)
  have hC_nn : (0 : ℝ) ≤ 2 * (2 * σsq) ^ k * ↑(Nat.factorial k) := by positivity
  have h_fn_nn : ∀ ω, (0 : ℝ) ≤ (X ω) ^ (2 * k) := by
    intro ω; rw [show 2 * k = k + k from by omega]; exact Even.pow_nonneg ⟨k, rfl⟩ _
  have h_ae_eq : (fun ω => (|X ω| ^ (2 * (k : ℝ)))) =ᵐ[μ] (fun ω => ((X ω) ^ (2 * k) : ℝ)) := by
    filter_upwards with ω
    rw [show (2 * (k : ℝ)) = ↑(2 * k) from by push_cast; ring, rpow_natCast]
    rw [show 2 * k = k + k from by omega]
    exact Even.pow_abs ⟨k, rfl⟩ (X ω)
  have h_lint_eq : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 * (k : ℝ))) ∂μ =
      ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * k)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [h_ae_eq] with ω hω
    rw [hω]
  rw [h_lint_eq] at h_lem14
  set C := 2 * (2 * σsq) ^ k * ↑(Nat.factorial k) with hC_def
  have h_boch_eq : ∫ ω, (X ω) ^ (2 * k) ∂μ =
      (∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * k)) ∂μ).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall h_fn_nn)
      (hX_meas.pow (2 * k))
  rw [h_boch_eq]
  have h_lint_ne_top : ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * k)) ∂μ ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) h_lem14
  calc (∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * k)) ∂μ).toReal
      ≤ (ENNReal.ofReal C).toReal := by
        rwa [ENNReal.toReal_le_toReal h_lint_ne_top ENNReal.ofReal_ne_top]
    _ = C := ENNReal.toReal_ofReal hC_nn

/-- For `X ~ subG(σ²)` and `|s| ≤ 1/(16σ²)`, the function `exp(|s · (X² - E[X²])|)` is
integrable. -/
theorem exp_abs_sq_centered_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq) (hX : IsSubGaussian X σsq μ)
    (s : ℝ) (hs : |s| ≤ 1 / (16 * σsq)) :
    Integrable (fun ω => rexp (|s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ)|)) μ := by
  set c := ∫ ω', (X ω') ^ 2 ∂μ with hc_def
  have hX_int := hX.1
  have hX_mean := hX.2.1
  have hX_exp := hX.2.2.1
  have hX_mgf := hX.2.2.2
  have hX_sq_int := sq_integrable_of_exp_integrable hX_int hX_exp
  have hc_nn : 0 ≤ c := integral_nonneg (fun ω => sq_nonneg _)


  have h_aesm : AEStronglyMeasurable (fun ω => rexp (|s * ((X ω) ^ 2 - c)|)) μ :=
    continuous_exp.comp_aestronglyMeasurable
      (continuous_abs.comp_aestronglyMeasurable
        ((hX_sq_int.sub (integrable_const c)).aestronglyMeasurable.const_mul s))

  refine ⟨h_aesm, ?_⟩
  rw [hasFiniteIntegral_def]


  set t := |s| with ht_def
  have ht_nn : 0 ≤ t := abs_nonneg s
  have ht_bound : t ≤ 1 / (16 * σsq) := hs

  set r := 2 * t * σsq with hr_def
  have hr_nn : 0 ≤ r := by positivity
  have hr_lt1 : r < 1 := by
    calc r = 2 * t * σsq := rfl
      _ ≤ 2 * (1 / (16 * σsq)) * σsq := by gcongr
      _ = 1 / 8 := by field_simp; ring
      _ < 1 := by norm_num

  calc ∫⁻ ω, ‖rexp (|s * ((X ω) ^ 2 - c)|)‖ₑ ∂μ
      = ∫⁻ ω, ENNReal.ofReal (rexp (|s * ((X ω) ^ 2 - c)|)) ∂μ := by
        congr 1; ext ω; rw [enorm_eq_ofReal (le_of_lt (exp_pos _))]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (rexp (t * (X ω) ^ 2 + t * c)) ∂μ := by
        apply MeasureTheory.lintegral_mono; intro ω
        apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp_of_le
        calc |s * ((X ω) ^ 2 - c)| = t * |(X ω) ^ 2 - c| := by rw [abs_mul, ht_def]
          _ ≤ t * ((X ω) ^ 2 + c) := by
              gcongr; exact (abs_sub _ _).trans (by
                rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc_nn])
          _ = t * (X ω) ^ 2 + t * c := by ring
    _ = ∫⁻ ω, (ENNReal.ofReal (rexp (t * c)) *
        ENNReal.ofReal (rexp (t * (X ω) ^ 2))) ∂μ := by
        congr 1; ext ω
        rw [← ENNReal.ofReal_mul (le_of_lt (exp_pos _)), ← Real.exp_add]
        congr 1; ring
    _ = ENNReal.ofReal (rexp (t * c)) *
        ∫⁻ ω, ENNReal.ofReal (rexp (t * (X ω) ^ 2)) ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := by
        apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top


        have h_exp_tsum : ∀ ω, rexp (t * (X ω) ^ 2) =
            ∑' k, (t * (X ω) ^ 2) ^ k / ↑(k.factorial) := by
          intro ω
          have hconv : rexp (t * (X ω) ^ 2) = NormedSpace.exp (t * (X ω) ^ 2) :=
            congr_fun Real.exp_eq_exp_ℝ _
          rw [hconv]
          exact (NormedSpace.expSeries_div_hasSum_exp (t * (X ω) ^ 2)).tsum_eq.symm

        have h_term_nn : ∀ ω k, 0 ≤ (t * (X ω) ^ 2) ^ k / ↑(k.factorial) := by
          intro ω k; positivity
        have h_summable : ∀ ω, Summable (fun k => (t * (X ω) ^ 2) ^ k / ↑(k.factorial)) := by
          intro ω
          exact (NormedSpace.expSeries_div_hasSum_exp (t * (X ω) ^ 2)).summable
        have h_ofReal_tsum : ∀ ω, ENNReal.ofReal (rexp (t * (X ω) ^ 2)) =
            ∑' k, ENNReal.ofReal ((t * (X ω) ^ 2) ^ k / ↑(k.factorial)) := by
          intro ω
          rw [h_exp_tsum ω]
          exact ENNReal.ofReal_tsum_of_nonneg (h_term_nn ω) (h_summable ω)

        have h_lint_eq : ∫⁻ ω, ENNReal.ofReal (rexp (t * (X ω) ^ 2)) ∂μ =
            ∑' k, ∫⁻ ω, ENNReal.ofReal ((t * (X ω) ^ 2) ^ k / ↑(k.factorial)) ∂μ := by
          conv_lhs => rw [show (fun ω => ENNReal.ofReal (rexp (t * (X ω) ^ 2))) =
            (fun ω => ∑' k, ENNReal.ofReal ((t * (X ω) ^ 2) ^ k / ↑(k.factorial))) from by
              ext ω; exact h_ofReal_tsum ω]
          exact lintegral_tsum (fun k => by
            apply AEMeasurable.ennreal_ofReal
            exact (((hX_int.aemeasurable.pow_const 2).const_mul t).pow_const k).div_const _)
        rw [h_lint_eq]


        apply lt_top_iff_ne_top.mpr
        apply ne_top_of_le_ne_top (show (ENNReal.ofReal (2 * (1 - r)⁻¹)) ≠ ⊤ from
          ENNReal.ofReal_ne_top)
        calc ∑' k, ∫⁻ ω, ENNReal.ofReal ((t * (X ω) ^ 2) ^ k / ↑(k.factorial)) ∂μ
            ≤ ∑' k, ENNReal.ofReal (2 * r ^ k) := by
              apply ENNReal.tsum_le_tsum; intro k
              by_cases hk : k = 0
              · subst hk; simp
              ·
                have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
                have h_moment := subgaussian_even_moment_bound hσ hX_int hX_mean hX_exp hX_mgf k hk_pos

                have h_fn_nn : ∀ ω, (0 : ℝ) ≤ (X ω) ^ (2 * k) := by
                  intro ω; rw [show 2 * k = k + k from by omega]
                  exact Even.pow_nonneg ⟨k, rfl⟩ _

                have h_term_eq : ∀ ω, (t * (X ω) ^ 2) ^ k / ↑(k.factorial) =
                    t ^ k / ↑(k.factorial) * (X ω) ^ (2 * k) := by
                  intro ω; rw [mul_pow, ← pow_mul]; ring

                calc ∫⁻ ω, ENNReal.ofReal ((t * (X ω) ^ 2) ^ k / ↑(k.factorial)) ∂μ
                    = ∫⁻ ω, ENNReal.ofReal (t ^ k / ↑(k.factorial) * (X ω) ^ (2 * k)) ∂μ := by
                      congr 1; ext ω; rw [h_term_eq]
                  _ = ∫⁻ ω, (ENNReal.ofReal (t ^ k / ↑(k.factorial)) *
                      ENNReal.ofReal ((X ω) ^ (2 * k))) ∂μ := by
                      congr 1; ext ω
                      rw [← ENNReal.ofReal_mul (by positivity)]
                  _ = ENNReal.ofReal (t ^ k / ↑(k.factorial)) *
                      ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 * k)) ∂μ := by
                      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                  _ ≤ ENNReal.ofReal (t ^ k / ↑(k.factorial)) *
                      ENNReal.ofReal (2 * (2 * σsq) ^ k * ↑(k.factorial)) := by
                      gcongr


                      have h_exp_abs_int : Integrable (fun ω => rexp (|X ω|)) μ := by
                        have h1 := hX_exp 1; simp only [one_mul] at h1
                        have h2 := hX_exp (-1); simp only [neg_one_mul] at h2
                        exact (h1.add h2).mono
                          (continuous_exp.comp_aestronglyMeasurable
                            hX_int.aestronglyMeasurable.norm) (by
                          filter_upwards with ω
                          simp only [Pi.add_apply]
                          have hsum_pos : 0 ≤ rexp (X ω) + rexp (-X ω) := by
                            linarith [exp_pos (X ω), exp_pos (-X ω)]
                          rw [Real.norm_of_nonneg (le_of_lt (exp_pos _)),
                              Real.norm_of_nonneg hsum_pos]
                          rcases le_or_gt 0 (X ω) with h | h
                          · rw [abs_of_nonneg h]; linarith [exp_pos (-X ω)]
                          · rw [abs_of_neg h]; linarith [exp_pos (X ω)])

                      have h_pow_le_exp : ∀ ω, (X ω) ^ (2 * k) ≤
                          ↑((2 * k).factorial) * rexp (|X ω|) := by
                        intro ω
                        have habs := abs_nonneg (X ω)
                        have h_sum := Real.sum_le_exp_of_nonneg habs (2 * k + 1)
                        have h_term : |X ω| ^ (2 * k) / ↑((2 * k).factorial) ≤
                            ∑ i ∈ Finset.range (2 * k + 1),
                              |X ω| ^ i / ↑(i.factorial) := by
                          apply @Finset.single_le_sum ℕ ℝ _ _ (fun i => |X ω| ^ i / ↑(i.factorial))
                          · intro i _; positivity
                          · exact Finset.mem_range.mpr (by omega)
                        have h1 : |X ω| ^ (2 * k) / ↑((2 * k).factorial) ≤ rexp (|X ω|) :=
                          le_trans h_term h_sum
                        have hfact_pos : (0 : ℝ) < ↑((2 * k).factorial) :=
                          Nat.cast_pos.mpr (Nat.factorial_pos _)
                        calc (X ω) ^ (2 * k)
                            = |X ω| ^ (2 * k) := by
                              rw [show 2 * k = k + k from by omega]
                              exact (Even.pow_abs ⟨k, rfl⟩ (X ω)).symm
                          _ ≤ ↑((2 * k).factorial) * rexp (|X ω|) := by
                              have h2 : |X ω| ^ (2 * k) ≤ rexp (|X ω|) * ↑((2 * k).factorial) := by
                                rwa [div_le_iff₀ hfact_pos] at h1
                              linarith [mul_comm (rexp (|X ω|)) (↑((2 * k).factorial) : ℝ)]

                      have h_int_pow : Integrable (fun ω => (X ω) ^ (2 * k)) μ :=
                        (h_exp_abs_int.const_mul (↑((2 * k).factorial) : ℝ)).mono
                          (hX_int.aestronglyMeasurable.pow (2 * k)) (by
                          filter_upwards with ω
                          rw [Real.norm_of_nonneg (h_fn_nn ω),
                            Real.norm_of_nonneg (by positivity)]
                          exact h_pow_le_exp ω)
                      rw [← ofReal_integral_eq_lintegral_ofReal h_int_pow
                        (Filter.Eventually.of_forall h_fn_nn)]
                      exact ENNReal.ofReal_le_ofReal h_moment
                  _ = ENNReal.ofReal (t ^ k / ↑(k.factorial) *
                      (2 * (2 * σsq) ^ k * ↑(k.factorial))) := by
                      rw [← ENNReal.ofReal_mul (by positivity)]
                  _ = ENNReal.ofReal (2 * r ^ k) := by
                      congr 1
                      have hfact_ne : (↑(k.factorial) : ℝ) ≠ 0 :=
                        Nat.cast_pos.mpr (Nat.factorial_pos k) |>.ne'
                      field_simp
                      rw [hr_def]; ring
          _ = ENNReal.ofReal (2 * (∑' k, r ^ k)) := by
              rw [show (fun k : ℕ => ENNReal.ofReal (2 * r ^ k)) =
                (fun k => ENNReal.ofReal (2 * r ^ k)) from rfl]
              rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
                    ((summable_geometric_of_lt_one hr_nn hr_lt1).mul_left 2),
                  tsum_mul_left]
          _ = ENNReal.ofReal (2 * (1 - r)⁻¹) := by
              congr 1; congr 1
              exact tsum_geometric_of_lt_one hr_nn hr_lt1

/-- Companion to `exp_abs_sq_centered_integrable`: integrability of
`exp(s · (X² - E[X²]))` for `|s|` small. -/
theorem exp_sq_centered_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq) (hX : IsSubGaussian X σsq μ)
    (s : ℝ) (hs : |s| ≤ 1 / (16 * σsq)) :
    Integrable (fun ω => rexp (s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ))) μ := by
  have h_abs := exp_abs_sq_centered_integrable hσ hX s hs
  have hf_aesm : AEStronglyMeasurable (fun ω => s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ)) μ := by
    apply AEStronglyMeasurable.const_mul
    apply AEStronglyMeasurable.sub
    · exact (hX.1.aestronglyMeasurable.pow 2)
    · exact aestronglyMeasurable_const
  exact h_abs.mono (continuous_exp.comp_aestronglyMeasurable hf_aesm) (by
    filter_upwards with ω
    simp only [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp_of_le (le_abs_self _))

/-- DCT-based Taylor-series expansion for the MGF of the centred square `X² - E[X²]`. -/
theorem dct_mgf_expansion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq)
    (hX : IsSubGaussian X σsq μ)
    (s : ℝ) (hs : |s| ≤ 1 / (16 * σsq)) :
    ∫ ω, rexp (s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ)) ∂μ
      ≤ 1 + ∑' (k : ℕ), |s| ^ (k + 2) *
          (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ (k + 2) ∂μ) / (k + 2).factorial := by
  set c := ∫ ω', (X ω') ^ 2 ∂μ with hc_def
  set Z : Ω → ℝ := fun ω => s * ((X ω) ^ 2 - c) with hZ_def

  have hX_int := hX.1
  have hX_exp := hX.2.2.1
  have hX_sq_int := sq_integrable_of_exp_integrable hX_int hX_exp

  have hZ_int : Integrable Z μ :=
    (hX_sq_int.sub (integrable_const c)).const_mul s

  have hZ_mean : ∫ ω, Z ω ∂μ = 0 := by
    simp only [hZ_def]
    rw [integral_const_mul, integral_sub hX_sq_int (integrable_const c), integral_const]
    have hmu : μ.real Set.univ = 1 := by
      simp [Measure.real, IsProbabilityMeasure.measure_univ]
    rw [hmu, one_smul]; ring


  have hZ_exp : Integrable (fun ω => rexp (Z ω)) μ :=
    exp_sq_centered_integrable hσ hX s hs

  have hZ_abs_exp : Integrable (fun ω => rexp (|Z ω|)) μ :=
    exp_abs_sq_centered_integrable hσ hX s hs

  have h_dct := dct_interchange_exp_tail hZ_int hZ_mean hZ_exp hZ_abs_exp


  suffices h_eq : ∀ k : ℕ, ∫ ω, |Z ω| ^ (k + 2) / ↑(k + 2).factorial ∂μ
      = |s| ^ (k + 2) * (∫ ω, |(X ω) ^ 2 - c| ^ (k + 2) ∂μ) / ↑(k + 2).factorial by
    calc ∫ ω, rexp (Z ω) ∂μ
        ≤ 1 + ∑' k, ∫ ω, |Z ω| ^ (k + 2) / ↑(k + 2).factorial ∂μ := h_dct
      _ = 1 + ∑' k, |s| ^ (k + 2) *
            (∫ ω, |(X ω) ^ 2 - c| ^ (k + 2) ∂μ) / ↑(k + 2).factorial := by
          congr 1; exact tsum_congr h_eq

  intro k
  have h_abs_eq : ∀ ω, |Z ω| ^ (k + 2) = |s| ^ (k + 2) * |(X ω) ^ 2 - c| ^ (k + 2) := by
    intro ω; simp only [hZ_def, abs_mul, mul_pow]

  have h_fn_eq : (fun ω => |Z ω| ^ (k + 2) / ↑(k + 2).factorial) =
      (fun ω => (|s| ^ (k + 2) / ↑(k + 2).factorial) * |(X ω) ^ 2 - c| ^ (k + 2)) := by
    ext ω; rw [h_abs_eq]; ring
  rw [h_fn_eq, integral_const_mul]
  ring

/-- Centering bound: `E[|X² - E[X²]|^k] ≤ 2^k · E[X^{2k}]`. -/
theorem centering_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    (hX_int : Integrable X μ)
    (hX_sq_int : Integrable (fun ω => X ω ^ 2) μ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ k ∂μ ≤
      2 ^ k * ∫ ω, (X ω) ^ (2 * k) ∂μ := by
  set c := ∫ ω, (X ω) ^ 2 ∂μ with hc_def
  have hc_nn : 0 ≤ c := integral_nonneg (fun ω => sq_nonneg _)
  have h_pow_eq : ∀ ω, (X ω ^ 2) ^ k = (X ω) ^ (2 * k) := fun ω => by rw [← pow_mul]

  have h_pw : ∀ ω, |(X ω) ^ 2 - c| ^ k ≤ 2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k) := by
    intro ω
    calc |(X ω) ^ 2 - c| ^ k
        ≤ (X ω ^ 2 + c) ^ k := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |(X ω) ^ 2 - c| ≤ |X ω ^ 2| + |c| := abs_sub _ _
            _ = X ω ^ 2 + c := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc_nn]
      _ ≤ 2 ^ (k - 1) * ((X ω ^ 2) ^ k + c ^ k) := add_pow_le (sq_nonneg _) hc_nn k
      _ = 2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k) := by rw [h_pow_eq]
  by_cases h_int_2k : Integrable (fun ω => (X ω) ^ (2 * k)) μ
  ·
    have h_bound_int : Integrable (fun ω => 2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k)) μ :=
      (h_int_2k.add (integrable_const _)).const_mul _
    have h_int_abs : Integrable (fun ω => |(X ω) ^ 2 - c| ^ k) μ :=
      h_bound_int.mono
        ((hX_sq_int.sub (integrable_const c)).aestronglyMeasurable.norm.pow k) (by
        filter_upwards with ω
        simp only [norm_pow, Real.norm_eq_abs, abs_abs]
        calc |(X ω) ^ 2 - c| ^ k ≤ 2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k) := h_pw ω
          _ ≤ ‖2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k)‖ := le_norm_self _)
    have h_jensen : c ^ k ≤ ∫ ω, (X ω) ^ (2 * k) ∂μ := by
      have := (convexOn_pow k).map_integral_le (continuous_pow k).continuousOn
        isClosed_Ici (by filter_upwards with ω; exact Set.mem_Ici.mpr (sq_nonneg _))
        hX_sq_int (by convert h_int_2k using 1; ext ω; exact h_pow_eq ω)
      calc c ^ k ≤ ∫ ω, (X ω ^ 2) ^ k ∂μ := this
        _ = ∫ ω, (X ω) ^ (2 * k) ∂μ := by congr 1; ext ω; exact h_pow_eq ω
    calc ∫ ω, |(X ω) ^ 2 - c| ^ k ∂μ
        ≤ ∫ ω, 2 ^ (k - 1) * ((X ω) ^ (2 * k) + c ^ k) ∂μ :=
          integral_mono h_int_abs h_bound_int (fun ω => h_pw ω)
      _ = 2 ^ (k - 1) * (∫ ω, (X ω) ^ (2 * k) ∂μ + c ^ k) := by
          rw [integral_const_mul]; congr 1
          rw [integral_add h_int_2k (integrable_const _)]; simp [integral_const]
      _ ≤ 2 ^ (k - 1) * (∫ ω, (X ω) ^ (2 * k) ∂μ + ∫ ω, (X ω) ^ (2 * k) ∂μ) := by gcongr
      _ = 2 ^ k * ∫ ω, (X ω) ^ (2 * k) ∂μ := by
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          simp [pow_succ']; ring
  ·
    have h_not_int_abs : ¬Integrable (fun ω => |(X ω) ^ 2 - c| ^ k) μ := by
      intro h_abs_int; apply h_int_2k
      have h_rev : ∀ ω, (X ω ^ 2) ^ k ≤
          2 ^ (k - 1) * (|(X ω) ^ 2 - c| ^ k + c ^ k) := by
        intro ω
        calc (X ω ^ 2) ^ k
            ≤ (|X ω ^ 2 - c| + c) ^ k := by
              apply pow_le_pow_left₀ (sq_nonneg _)
              calc X ω ^ 2 ≤ |X ω ^ 2| := le_abs_self _
                _ = |(X ω ^ 2 - c) + c| := by congr 1; ring
                _ ≤ |X ω ^ 2 - c| + |c| := abs_add_le _ _
                _ = |X ω ^ 2 - c| + c := by rw [abs_of_nonneg hc_nn]
          _ ≤ 2 ^ (k - 1) * (|X ω ^ 2 - c| ^ k + c ^ k) :=
              add_pow_le (abs_nonneg _) hc_nn k
      exact ((h_abs_int.add (integrable_const (c ^ k))).const_mul _).mono
        (hX_int.aestronglyMeasurable.pow (2 * k)) (by
        filter_upwards with ω
        rw [show ‖(X ω) ^ (2 * k)‖ = (X ω ^ 2) ^ k from by
          rw [h_pow_eq, Real.norm_of_nonneg]
          rw [← h_pow_eq]; exact pow_nonneg (sq_nonneg _) _]
        calc (X ω ^ 2) ^ k
            ≤ 2 ^ (k - 1) * (|(X ω) ^ 2 - c| ^ k + c ^ k) := h_rev ω
          _ ≤ ‖2 ^ (k - 1) * (|(X ω) ^ 2 - c| ^ k + c ^ k)‖ := le_norm_self _)
    rw [integral_undef h_not_int_abs, integral_undef h_int_2k]; simp

/-- Per-term geometric bound for the MGF expansion of `X² - E[X²]`: each term is
bounded by `(8 |s| σ²)^{k+2}`. -/
theorem per_term_mgf_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq)
    (hX : IsSubGaussian X σsq μ)
    (s : ℝ) (k : ℕ) :
    |s| ^ (k + 2) *
      (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ (k + 2) ∂μ) / (k + 2).factorial
    ≤ (8 * |s| * σsq) ^ (k + 2) := by
  set m := k + 2 with hm_def
  have hm : 1 ≤ m := by omega

  have hX_int := hX.1
  have hX_mean := hX.2.1
  have hX_exp := hX.2.2.1
  have hX_mgf := hX.2.2.2
  have hX_sq_int := sq_integrable_of_exp_integrable hX_int hX_exp

  have h_center := centering_moment_bound hX_int hX_sq_int m hm

  have h_moment := subgaussian_even_moment_bound hσ hX_int hX_mean hX_exp hX_mgf m hm

  have h_combined : ∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ m ∂μ ≤
      2 ^ m * (2 * (2 * σsq) ^ m * ↑(Nat.factorial m)) := by
    calc ∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ m ∂μ
        ≤ 2 ^ m * ∫ ω, (X ω) ^ (2 * m) ∂μ := h_center
      _ ≤ 2 ^ m * (2 * (2 * σsq) ^ m * ↑(Nat.factorial m)) := by gcongr


  calc |s| ^ m *
        (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ m ∂μ) / ↑(Nat.factorial m)
      ≤ |s| ^ m *
        (2 ^ m * (2 * (2 * σsq) ^ m * ↑(Nat.factorial m))) / ↑(Nat.factorial m) := by
        gcongr
    _ ≤ (8 * |s| * σsq) ^ m := by

        have hfact_ne : (↑(Nat.factorial m) : ℝ) ≠ 0 :=
          Nat.cast_pos.mpr (Nat.factorial_pos m) |>.ne'
        have hlhs : |s| ^ m * (2 ^ m * (2 * (2 * σsq) ^ m * ↑(Nat.factorial m))) /
            ↑(Nat.factorial m) = |s| ^ m * (2 ^ m * (2 * (2 * σsq) ^ m)) := by field_simp
        rw [hlhs]

        have h_eq : |s| ^ m * (2 ^ m * (2 * (2 * σsq) ^ m)) = 2 * (4 * |s| * σsq) ^ m := by
          simp only [mul_pow]
          rw [show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m from by rw [← mul_pow]; norm_num]
          ring
        rw [h_eq, show (8 : ℝ) * |s| * σsq = 2 * (4 * |s| * σsq) from by ring]

        calc 2 * (4 * |s| * σsq) ^ m
            ≤ 2 ^ m * (4 * |s| * σsq) ^ m := by
              gcongr
              calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
                _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm
          _ = (2 * (4 * |s| * σsq)) ^ m := (mul_pow _ _ _).symm

/-- Geometric series bound: `∑_{k≥0} (8|s|σ²)^{k+2} ≤ 128 s² σ^4` when `|s|` is small. -/
theorem geometric_series_bound
    (s σsq : ℝ) (hσ : 0 < σsq) (hs : |s| ≤ 1 / (16 * σsq)) :
    ∑' (k : ℕ), (8 * |s| * σsq) ^ (k + 2) ≤ 128 * s ^ 2 * σsq ^ 2 := by
  have h8sσ_nn : 0 ≤ 8 * |s| * σsq := by positivity
  have h8sσ_le : 8 * |s| * σsq ≤ 1 / 2 := by
    calc 8 * |s| * σsq ≤ 8 * (1 / (16 * σsq)) * σsq := by gcongr
      _ = 1 / 2 := by field_simp; ring
  have h8sσ_lt1 : 8 * |s| * σsq < 1 := by linarith
  rw [show (fun k : ℕ => (8 * |s| * σsq) ^ (k + 2)) =
    (fun k => (8 * |s| * σsq) ^ 2 * (8 * |s| * σsq) ^ k) from by ext k; ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h8sσ_nn h8sσ_lt1]
  have h_denom : 0 < 1 - 8 * |s| * σsq := by linarith
  have h_inv_le : (1 - 8 * |s| * σsq)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h_denom (by norm_num : (0:ℝ) < 2)]
    linarith
  calc (8 * |s| * σsq) ^ 2 * (1 - 8 * |s| * σsq)⁻¹
      ≤ (8 * |s| * σsq) ^ 2 * 2 := by gcongr
    _ = 128 * |s| ^ 2 * σsq ^ 2 := by ring
    _ = 128 * s ^ 2 * σsq ^ 2 := by rw [sq_abs]

/-- Analytical MGF bound for `Z = X² - E[X²]` when `X ~ subG(σ²)`:
`E[exp(sZ)] ≤ 1 + 128 s² σ^4` for `|s| ≤ 1/(16σ²)`. -/
theorem analytical_mgf_bound_for_centered_square
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq)
    (hX : IsSubGaussian X σsq μ)
    (s : ℝ) (hs : |s| ≤ 1 / (16 * σsq)) :
    ∫ ω, Real.exp (s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ)) ∂μ
      ≤ 1 + 128 * s ^ 2 * σsq ^ 2 := by

  have h_dct := dct_mgf_expansion hσ hX s hs

  have h_per_term : ∀ k : ℕ,
      |s| ^ (k + 2) *
        (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ (k + 2) ∂μ) / (k + 2).factorial
      ≤ (8 * |s| * σsq) ^ (k + 2) :=
    fun k => per_term_mgf_bound hσ hX s k

  have h_geom := geometric_series_bound s σsq hσ hs

  have h_tsum_le : ∑' (k : ℕ), |s| ^ (k + 2) *
      (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ (k + 2) ∂μ) / (k + 2).factorial
      ≤ ∑' (k : ℕ), (8 * |s| * σsq) ^ (k + 2) := by
    have h8sσ_nn : 0 ≤ 8 * |s| * σsq := by positivity
    have h8sσ_lt1 : 8 * |s| * σsq < 1 := by
      calc 8 * |s| * σsq ≤ 8 * (1 / (16 * σsq)) * σsq := by gcongr
        _ = 1 / 2 := by field_simp; ring
        _ < 1 := by norm_num
    have h_geom_summable : Summable (fun k => (8 * |s| * σsq) ^ (k + 2)) := by
      have : (fun k : ℕ => (8 * |s| * σsq) ^ (k + 2)) =
          (fun k => (8 * |s| * σsq) ^ 2 * (8 * |s| * σsq) ^ k) := by ext k; ring
      rw [this]
      exact (summable_geometric_of_lt_one h8sσ_nn h8sσ_lt1).mul_left _
    have h_f_summable : Summable (fun k => |s| ^ (k + 2) *
        (∫ ω, |(X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ| ^ (k + 2) ∂μ) / (k + 2).factorial) :=
      Summable.of_nonneg_of_le
        (fun k => by
          apply div_nonneg
          · apply mul_nonneg (pow_nonneg (abs_nonneg s) _)
            exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
          · exact Nat.cast_nonneg _)
        h_per_term h_geom_summable
    exact h_f_summable.tsum_mono h_geom_summable h_per_term
  linarith

/-- **Lemma 1.12**: For `X ~ subG(σ²)`, the centred square `Z = X² - E[X²]` is
sub-exponential with parameter `16σ²`, i.e. `Z ~ subE(16σ²)`. -/
theorem lemma_1_12_square_subgaussian_is_subexponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σsq : ℝ}
    (hσ : 0 < σsq)
    (hX : IsSubGaussian X σsq μ) :
    @IsSubExponential Ω _ μ _
      (fun ω => (X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ) (16 * σsq) := by
  have hX_sq_int : Integrable (fun ω => X ω ^ 2) μ :=
    sq_integrable_of_exp_integrable hX.1 hX.2.2.1
  refine ⟨by linarith [mul_pos (by norm_num : (0:ℝ) < 16) hσ], ?_, ?_, ?_⟩

  · exact Integrable.sub hX_sq_int (integrable_const _)

  · rw [integral_sub hX_sq_int (integrable_const _)]
    simp [integral_const]


  · intro s hs
    calc ∫ ω, rexp (s * ((X ω) ^ 2 - ∫ ω', (X ω') ^ 2 ∂μ)) ∂μ
        ≤ 1 + 128 * s ^ 2 * σsq ^ 2 :=
          analytical_mgf_bound_for_centered_square hσ hX s hs
      _ ≤ rexp (128 * s ^ 2 * σsq ^ 2) := by
          linarith [Real.add_one_le_exp (128 * s ^ 2 * σsq ^ 2)]
      _ = rexp (s ^ 2 * (16 * σsq) ^ 2 / 2) := by ring_nf
