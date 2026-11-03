/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8

open MeasureTheory InformationTheory

set_option maxHeartbeats 1200000

noncomputable section

namespace TotalVariation

/-- For any measurable `T`, the signed mass difference `P₀(T) - P₁(T)` is
maximised by the set `{dP₁/dμ < dP₀/dμ}` where `dP₀/dμ` dominates. -/
lemma measure_diff_le_of_positive_set {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ)
    (T : Set Ω) (hT : MeasurableSet T) :
    (P₀ T).toReal - (P₁ T).toReal ≤
    (P₀ {ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}).toReal -
    (P₁ {ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}).toReal := by
  set R := {ω : Ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}
  set f := fun ω => (P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal
  have hR_meas : MeasurableSet R :=
    measurableSet_lt (Measure.measurable_rnDeriv P₁ μ) (Measure.measurable_rnDeriv P₀ μ)
  have hf_int : Integrable f μ :=
    Integrable.sub Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
  have h_as_int : ∀ S : Set Ω, MeasurableSet S →
      (P₀ S).toReal - (P₁ S).toReal = ∫ x in S, f x ∂μ := by
    intro S hS; simp only [f]
    rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn,
        Measure.setIntegral_toReal_rnDeriv hac₀, Measure.setIntegral_toReal_rnDeriv hac₁]; rfl
  rw [h_as_int T hT, h_as_int R hR_meas]
  have hT_split : ∫ x in T, f x ∂μ =
      ∫ x in T ∩ R, f x ∂μ + ∫ x in T ∩ Rᶜ, f x ∂μ := by
    conv_lhs => rw [show T = (T ∩ R) ∪ (T ∩ Rᶜ) from by ext x; simp]
    exact setIntegral_union₀ (Disjoint.aedisjoint disjoint_inf_sdiff)
      (hT.inter hR_meas.compl).nullMeasurableSet hf_int.integrableOn hf_int.integrableOn
  have hR_split : ∫ x in R, f x ∂μ =
      ∫ x in R ∩ T, f x ∂μ + ∫ x in R ∩ Tᶜ, f x ∂μ := by
    conv_lhs => rw [show R = (R ∩ T) ∪ (R ∩ Tᶜ) from by ext x; simp]
    exact setIntegral_union₀ (Disjoint.aedisjoint disjoint_inf_sdiff)
      (hR_meas.inter hT.compl).nullMeasurableSet hf_int.integrableOn hf_int.integrableOn
  rw [hT_split, hR_split, Set.inter_comm T R]
  linarith [
    setIntegral_nonneg_ae (hR_meas.inter hT.compl) (by
      filter_upwards [Measure.rnDeriv_lt_top P₀ μ] with ω hω_top
      intro hω_mem
      simp only [Set.mem_inter_iff, R, Set.mem_setOf_eq] at hω_mem
      exact sub_nonneg.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) (le_of_lt hω_mem.1))),
    setIntegral_nonpos_ae (hT.inter hR_meas.compl) (by
      filter_upwards [Measure.rnDeriv_lt_top P₁ μ] with ω hω_top
      intro hω_mem
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, R, Set.mem_setOf_eq, not_lt] at hω_mem
      exact sub_nonpos.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) hω_mem.2))
  ]

/-- The total variation distance equals the signed mass difference on the
positivity set `{dP₁/dμ < dP₀/dμ}`. -/
lemma tvDist_eq_diff_on_positive_set {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ) :
    Chapter5.TVNP.tvDist P₀ P₁ = (P₀ {ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}).toReal -
                   (P₁ {ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}).toReal := by
  set R := {ω : Ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}
  set f := fun ω => (P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal
  have hR_meas : MeasurableSet R :=
    measurableSet_lt (Measure.measurable_rnDeriv P₁ μ) (Measure.measurable_rnDeriv P₀ μ)
  have hval_nonneg : 0 ≤ (P₀ R).toReal - (P₁ R).toReal := by
    have hR_int : ∫ x in R, f x ∂μ = (P₀ R).toReal - (P₁ R).toReal := by
      simp only [f]
      rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
          Measure.integrable_toReal_rnDeriv.integrableOn,
          Measure.setIntegral_toReal_rnDeriv hac₀, Measure.setIntegral_toReal_rnDeriv hac₁]; rfl
    rw [← hR_int]
    apply setIntegral_nonneg_ae hR_meas
    filter_upwards [Measure.rnDeriv_lt_top P₀ μ] with ω hω_top
    intro hω_mem
    exact sub_nonneg.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) (le_of_lt hω_mem))
  have hge : (P₀ R).toReal - (P₁ R).toReal ≤ Chapter5.TVNP.tvDist P₀ P₁ := by
    have h := Chapter5.TVNP.tvDist_ge_abs_diff P₀ P₁ R hR_meas
    simp only [Chapter5.TVNP.tvDist] at h ⊢
    linarith [abs_of_nonneg hval_nonneg]
  have hle : Chapter5.TVNP.tvDist P₀ P₁ ≤ (P₀ R).toReal - (P₁ R).toReal := by
    simp only [Chapter5.TVNP.tvDist]
    apply csSup_le
    · exact ⟨|(P₀ Set.univ).toReal - (P₁ Set.univ).toReal|,
        Set.univ, MeasurableSet.univ, rfl⟩
    intro x hx
    obtain ⟨T, hT_meas, hx_eq⟩ := hx
    rw [hx_eq, abs_le]
    constructor
    · have hTc := measure_diff_le_of_positive_set P₀ P₁ μ hac₀ hac₁ Tᶜ hT_meas.compl
      have hcompl₀ : (P₀ Tᶜ).toReal = 1 - (P₀ T).toReal := by
        rw [measure_compl hT_meas (measure_ne_top P₀ _),
            ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₀ _),
            measure_univ, ENNReal.toReal_one]
      have hcompl₁ : (P₁ Tᶜ).toReal = 1 - (P₁ T).toReal := by
        rw [measure_compl hT_meas (measure_ne_top P₁ _),
            ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₁ _),
            measure_univ, ENNReal.toReal_one]
      linarith
    · exact measure_diff_le_of_positive_set P₀ P₁ μ hac₀ hac₁ T hT_meas
  linarith

/-- Variational form of TV distance in terms of Radon–Nikodym densities:
`TV(P₀, P₁) = sup_S |∫_S (dP₀/dμ - dP₁/dμ) dμ|`. -/
theorem tvDist_eq_sup_abs_integral {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ) :
    Chapter5.TVNP.tvDist P₀ P₁ = sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧
      x = |∫ ω in S, ((P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal) ∂μ|} := by
  have h_as_int : ∀ S : Set Ω, MeasurableSet S →
      ∫ ω in S, ((P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal) ∂μ =
      (P₀ S).toReal - (P₁ S).toReal := by
    intro S hS
    rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn,
        Measure.setIntegral_toReal_rnDeriv hac₀, Measure.setIntegral_toReal_rnDeriv hac₁]; rfl
  simp only [Chapter5.TVNP.tvDist]
  congr 1; ext x; simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, hS, by rw [hx, h_as_int S hS]⟩
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, hS, by rw [hx, h_as_int S hS]⟩

/-- Half-`L¹` representation of TV distance:
`TV(P₀, P₁) = ½ ∫ |dP₀/dμ - dP₁/dμ| dμ`. -/
theorem tvDist_eq_half_l1 {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ) :
    Chapter5.TVNP.tvDist P₀ P₁ =
      (1 / 2) * ∫ x, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ := by
  set R := {ω : Ω | P₁.rnDeriv μ ω < P₀.rnDeriv μ ω}
  have hR_meas : MeasurableSet R :=
    measurableSet_lt (Measure.measurable_rnDeriv P₁ μ) (Measure.measurable_rnDeriv P₀ μ)
  have htv := tvDist_eq_diff_on_positive_set P₀ P₁ μ hac₀ hac₁
  have hintegrable : Integrable (fun x => |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal|) μ :=
    (Integrable.sub Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv).abs
  have hsplit : ∫ x, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ =
      ∫ x in R, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ +
      ∫ x in Rᶜ, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ :=
    (integral_add_compl hR_meas hintegrable).symm
  have hR_eq : ∫ x in R, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ =
      ∫ x in R, ((P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal) ∂μ := by
    apply setIntegral_congr_ae hR_meas
    filter_upwards [Measure.rnDeriv_lt_top P₀ μ] with ω hω_top
    intro hω
    exact abs_of_nonneg (sub_nonneg.mpr ((ENNReal.toReal_le_toReal
      (ne_top_of_lt hω) (ne_top_of_lt hω_top)).mpr (le_of_lt hω)))
  have hRc_eq : ∫ x in Rᶜ, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ =
      ∫ x in Rᶜ, ((P₁.rnDeriv μ x).toReal - (P₀.rnDeriv μ x).toReal) ∂μ := by
    apply setIntegral_congr_ae hR_meas.compl
    filter_upwards [Measure.rnDeriv_lt_top P₁ μ] with ω hω_top
    intro hω
    have hle : P₀.rnDeriv μ ω ≤ P₁.rnDeriv μ ω := by
      simp only [R, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω; exact hω
    have hsub : (P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal ≤ 0 :=
      sub_nonpos.mpr ((ENNReal.toReal_le_toReal
        (ne_top_of_lt (lt_of_le_of_lt hle hω_top)) (ne_top_of_lt hω_top)).mpr hle)
    rw [abs_of_nonpos hsub]; ring
  have hR_val : ∫ x in R, ((P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal) ∂μ =
      P₀.real R - P₁.real R := by
    rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn,
        Measure.setIntegral_toReal_rnDeriv hac₀, Measure.setIntegral_toReal_rnDeriv hac₁]
  have hRc_val : ∫ x in Rᶜ, ((P₁.rnDeriv μ x).toReal - (P₀.rnDeriv μ x).toReal) ∂μ =
      P₁.real Rᶜ - P₀.real Rᶜ := by
    rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn,
        Measure.setIntegral_toReal_rnDeriv hac₁, Measure.setIntegral_toReal_rnDeriv hac₀]
  have hRc_val2 : P₁.real Rᶜ - P₀.real Rᶜ = P₀.real R - P₁.real R := by
    simp only [Measure.real]
    have h1 : (P₁ Rᶜ).toReal = 1 - (P₁ R).toReal := by
      rw [measure_compl hR_meas (measure_ne_top P₁ _),
          ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₁ _),
          measure_univ, ENNReal.toReal_one]
    have h2 : (P₀ Rᶜ).toReal = 1 - (P₀ R).toReal := by
      rw [measure_compl hR_meas (measure_ne_top P₀ _),
          ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₀ _),
          measure_univ, ENNReal.toReal_one]
    linarith
  have htv' : Chapter5.TVNP.tvDist P₀ P₁ = P₀.real R - P₁.real R := htv
  rw [htv', hsplit, hR_eq, hRc_eq, hR_val, hRc_val, hRc_val2]
  ring

/-- Dual representation:
`TV(P₀, P₁) = 1 - ∫ min(dP₀/dμ, dP₁/dμ) dμ`, the optimal-test error formula. -/
theorem tvDist_eq_one_minus_min {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ) :
    Chapter5.TVNP.tvDist P₀ P₁ =
      1 - ∫ x, min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal ∂μ := by
  have htv_half := tvDist_eq_half_l1 P₀ P₁ μ hac₀ hac₁
  have h0 : Integrable (fun x => (P₀.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv (μ := P₀) (ν := μ)
  have h1 : Integrable (fun x => (P₁.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv (μ := P₁) (ν := μ)
  have hmin : Integrable (fun x => min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal) μ :=
    h0.inf h1
  have hpw : ∀ x : Ω, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| =
    (P₀.rnDeriv μ x).toReal + (P₁.rnDeriv μ x).toReal -
      2 * min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal := by
    intro x
    rcases le_total (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]; ring
  have habs_eq : ∫ x, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ =
      ∫ x, (P₀.rnDeriv μ x).toReal ∂μ + ∫ x, (P₁.rnDeriv μ x).toReal ∂μ -
      2 * ∫ x, min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal ∂μ := by
    simp_rw [hpw]
    have h_sub : ∫ x, ((P₀.rnDeriv μ x).toReal + (P₁.rnDeriv μ x).toReal -
        2 * min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal) ∂μ =
        ∫ x, ((P₀.rnDeriv μ x).toReal + (P₁.rnDeriv μ x).toReal) ∂μ -
        ∫ x, (2 * min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal) ∂μ :=
      integral_sub (h0.add h1) (hmin.const_mul 2)
    have h_add : ∫ x, ((P₀.rnDeriv μ x).toReal + (P₁.rnDeriv μ x).toReal) ∂μ =
        ∫ x, (P₀.rnDeriv μ x).toReal ∂μ + ∫ x, (P₁.rnDeriv μ x).toReal ∂μ :=
      integral_add h0 h1
    have h_const_mul : ∫ x, (2 * min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal) ∂μ =
        2 * ∫ x, min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal ∂μ :=
      integral_const_mul 2 _
    linarith
  have hint0 : ∫ x, (P₀.rnDeriv μ x).toReal ∂μ = 1 := by
    have h := Measure.integral_toReal_rnDeriv hac₀
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at h; exact h
  have hint1 : ∫ x, (P₁.rnDeriv μ x).toReal ∂μ = 1 := by
    have h := Measure.integral_toReal_rnDeriv hac₁
    simp only [Measure.real, measure_univ, ENNReal.toReal_one] at h; exact h
  rw [htv_half, habs_eq, hint0, hint1]
  ring

/-- Neyman–Pearson equality: the sum of type-I and type-II errors of the
likelihood-ratio test equals `1 - TV(P₀, P₁)`. -/
theorem tvDist_eq_testing_error_lr {Ω : Type*} {_ : MeasurableSpace Ω}
    (P₀ P₁ ν : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (hν₀ : P₀.AbsolutelyContinuous ν) (hν₁ : P₁.AbsolutelyContinuous ν)
    [SigmaFinite ν] :
    (P₀ {ω | Chapter5.TVNP.lrTest P₁ P₀ ν ω = true}).toReal +
      (P₁ {ω | Chapter5.TVNP.lrTest P₁ P₀ ν ω = false}).toReal =
      1 - Chapter5.TVNP.tvDist P₀ P₁ :=
  Chapter5.TVNP.neyman_pearson_equality P₀ P₁ ν inferInstance inferInstance hν₀ hν₁

/-- Bundled Definition–Proposition 5.4 on the total variation distance: it
admits four equivalent representations — variational, half-`L¹`, complement of
the affinity, and as the optimal Neyman–Pearson testing error. -/
theorem defProp_5_4 {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ μ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] [SigmaFinite μ]
    (hac₀ : P₀ ≪ μ) (hac₁ : P₁ ≪ μ) :

    (Chapter5.TVNP.tvDist P₀ P₁ = sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧
      x = |∫ ω in S, ((P₀.rnDeriv μ ω).toReal - (P₁.rnDeriv μ ω).toReal) ∂μ|})
    ∧

    (Chapter5.TVNP.tvDist P₀ P₁ =
      (1 / 2) * ∫ x, |(P₀.rnDeriv μ x).toReal - (P₁.rnDeriv μ x).toReal| ∂μ)
    ∧

    (Chapter5.TVNP.tvDist P₀ P₁ =
      1 - ∫ x, min (P₀.rnDeriv μ x).toReal (P₁.rnDeriv μ x).toReal ∂μ)
    ∧

    ((P₀ {ω | Chapter5.TVNP.lrTest P₁ P₀ μ ω = true}).toReal +
      (P₁ {ω | Chapter5.TVNP.lrTest P₁ P₀ μ ω = false}).toReal =
      1 - Chapter5.TVNP.tvDist P₀ P₁) :=
  ⟨tvDist_eq_sup_abs_integral P₀ P₁ μ hac₀ hac₁,
   tvDist_eq_half_l1 P₀ P₁ μ hac₀ hac₁,
   tvDist_eq_one_minus_min P₀ P₁ μ hac₀ hac₁,
   tvDist_eq_testing_error_lr P₀ P₁ μ hac₀ hac₁⟩

end TotalVariation
