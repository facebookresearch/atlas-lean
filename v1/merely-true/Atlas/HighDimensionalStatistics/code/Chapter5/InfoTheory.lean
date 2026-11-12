/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space
import Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory InformationTheory Real

noncomputable section

namespace InfoTheory

/-- Total variation distance between probability measures `P₀` and `P₁` on a measurable space,
defined as the supremum of `|P₀ S - P₁ S|` over measurable sets `S`. (Definition 5.4.) -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ : Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧ x = |(P₀ S).toReal - (P₁ S).toReal|}

/-- Real-valued version of the Kullback–Leibler divergence `klDiv P Q`, obtained by
taking `toReal` of the `ℝ≥0∞`-valued divergence. -/
noncomputable def klDiv_real {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

/-- Bhattacharyya coefficient `BC(P, Q) = ∫ √(dP/dQ) dQ` between two measures. -/
noncomputable def bhattacharyyaCoeff {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  ∫ ω, Real.sqrt (P.rnDeriv Q ω).toReal ∂Q


/-- The pointwise inequality `klFun t ≥ (√t - 1)²` for all `t ≥ 0`, used to relate the
KL divergence to the Hellinger/Bhattacharyya distance. -/
lemma klFun_ge_sq_sqrt_sub_one {t : ℝ} (ht : 0 ≤ t) :
    klFun t ≥ (Real.sqrt t - 1) ^ 2 := by
  rw [ge_iff_le, ← sub_nonneg]
  by_cases ht0 : t = 0
  · simp [ht0, klFun, Real.sqrt_zero, Real.log_zero]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
    have hsqrt_nn : 0 ≤ Real.sqrt t := le_of_lt hsqrt_pos
    have hklsqrt : 0 ≤ klFun (Real.sqrt t) := klFun_nonneg hsqrt_nn
    suffices h : klFun t - (Real.sqrt t - 1) ^ 2 = 2 * Real.sqrt t * klFun (Real.sqrt t) by
      rw [h]; exact mul_nonneg (mul_nonneg (by norm_num) hsqrt_nn) hklsqrt

    set s := Real.sqrt t with hs_def
    have hss : s * s = t := Real.mul_self_sqrt ht
    have hlog_s : Real.log s = Real.log t / 2 := Real.log_sqrt ht
    simp only [klFun]


    rw [hlog_s]
    have h_sq : (s - 1) ^ 2 = s * s - 2 * s + 1 := by ring
    have h_rhs : 2 * s * (s * (Real.log t / 2) + 1 - s) =
        s * s * Real.log t + 2 * s - 2 * (s * s) := by ring
    have h_prod : s * s * Real.log t = t * Real.log t := by rw [hss]
    linarith

/-- Lower bound `KL(P, Q) ≥ 2 - 2·BC(P, Q)` relating Kullback–Leibler divergence to the
Bhattacharyya coefficient, valid when `P ≪ Q` and the KL divergence is finite. -/
lemma kl_ge_two_sub_two_bc {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q)
    (hfin : klDiv P Q ≠ ⊤) :
    klDiv_real P Q ≥ 2 - 2 * bhattacharyyaCoeff P Q := by
  unfold klDiv_real bhattacharyyaCoeff
  rw [toReal_klDiv_eq_integral_klFun hac]


  have h_int_llr : Integrable (llr P Q) P := by
    by_contra h; exact hfin (klDiv_of_not_integrable h)
  have h_int_klFun : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q :=
    (integrable_klFun_rnDeriv_iff hac).mpr h_int_llr
  have h_f_nn : ∀ ω, 0 ≤ (P.rnDeriv Q ω).toReal := fun ω => ENNReal.toReal_nonneg
  have h_int_f : Integrable (fun ω => (P.rnDeriv Q ω).toReal) Q :=
    Measure.integrable_toReal_rnDeriv

  have h_meas_sqrt : Measurable (fun ω => Real.sqrt (P.rnDeriv Q ω).toReal) :=
    (Measure.measurable_rnDeriv P Q).ennreal_toReal.sqrt

  have h_sqrt_le : ∀ ω, ‖Real.sqrt (P.rnDeriv Q ω).toReal‖ ≤
      ‖(fun ω => (P.rnDeriv Q ω).toReal + 1) ω‖ := by
    intro ω
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (by linarith [h_f_nn ω])]
    have h_sq := Real.mul_self_sqrt (h_f_nn ω)
    have h_sqrt_nn := Real.sqrt_nonneg (P.rnDeriv Q ω).toReal
    nlinarith [sq_nonneg (Real.sqrt (P.rnDeriv Q ω).toReal - 1)]
  have h_int_sqrt : Integrable (fun ω => Real.sqrt (P.rnDeriv Q ω).toReal) Q :=
    (h_int_f.add (integrable_const 1)).mono
      h_meas_sqrt.aestronglyMeasurable
      (ae_of_all Q h_sqrt_le)

  have h_int_f_eq : ∫ ω, (P.rnDeriv Q ω).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, measureReal_def,
        IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]

  have h_int_one : ∫ _ : Ω, (1 : ℝ) ∂Q = 1 := by
    rw [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
        ENNReal.toReal_one, smul_eq_mul, mul_one]

  have h_mono : ∫ ω, (Real.sqrt (P.rnDeriv Q ω).toReal - 1) ^ 2 ∂Q ≤
      ∫ ω, klFun (P.rnDeriv Q ω).toReal ∂Q := by
    apply integral_mono_of_nonneg
    · exact ae_of_all Q (fun ω => sq_nonneg _)
    · exact h_int_klFun
    · exact ae_of_all Q (fun ω => (klFun_ge_sq_sqrt_sub_one (h_f_nn ω)).le)

  have h_expand : ∫ ω, (Real.sqrt (P.rnDeriv Q ω).toReal - 1) ^ 2 ∂Q =
      2 - 2 * ∫ ω, Real.sqrt (P.rnDeriv Q ω).toReal ∂Q := by

    have h_pw : ∀ ω, (Real.sqrt (P.rnDeriv Q ω).toReal - 1) ^ 2 =
        (P.rnDeriv Q ω).toReal + 1 - 2 * Real.sqrt (P.rnDeriv Q ω).toReal := by
      intro ω
      have h_sq := Real.mul_self_sqrt (h_f_nn ω)
      have h_sqrt_nn := Real.sqrt_nonneg (P.rnDeriv Q ω).toReal
      nlinarith [sq_abs (Real.sqrt (P.rnDeriv Q ω).toReal - 1)]
    simp_rw [h_pw]
    have h_int_sum : Integrable (fun ω => (P.rnDeriv Q ω).toReal + 1) Q :=
      h_int_f.add (integrable_const 1)
    have h_int_2sqrt : Integrable (fun ω =>
        2 * Real.sqrt (P.rnDeriv Q ω).toReal) Q :=
      h_int_sqrt.const_mul 2
    rw [integral_sub h_int_sum h_int_2sqrt,
        integral_add h_int_f (integrable_const 1),
        integral_const_mul]
    rw [h_int_f_eq, h_int_one]
    ring

  linarith

/-- The Bhattacharyya coefficient is nonnegative. -/
lemma bhattacharyyaCoeff_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : 0 ≤ bhattacharyyaCoeff P Q := by
  unfold bhattacharyyaCoeff
  apply integral_nonneg
  intro ω
  exact Real.sqrt_nonneg _

/-- Cauchy–Schwarz inequality for integrals of nonnegative functions:
`(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. -/
lemma cauchy_schwarz_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ)
    (hf_nn : ∀ ω, 0 ≤ f ω) (hg_nn : ∀ ω, 0 ≤ g ω)
    (hf_int : Integrable (fun ω => f ω ^ 2) μ)
    (hg_int : Integrable (fun ω => g ω ^ 2) μ)
    (hfg_int : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  set A := ∫ ω, f ω ^ 2 ∂μ
  set B := ∫ ω, f ω * g ω ∂μ
  set C := ∫ ω, g ω ^ 2 ∂μ


  suffices h : discrim C (2 * B) A ≤ 0 by
    unfold discrim at h; nlinarith
  apply discrim_le_zero
  intro t
  have h_nonneg : 0 ≤ ∫ ω, (f ω + t * g ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have h_eq : ∫ ω, (f ω + t * g ω) ^ 2 ∂μ = A + 2 * t * B + t ^ 2 * C := by
    have key : (fun ω => (f ω + t * g ω) ^ 2) =
        (fun ω => f ω ^ 2 + 2 * t * (f ω * g ω) + t ^ 2 * g ω ^ 2) := by
      ext ω; ring
    rw [key]
    have h1 : Integrable (fun ω => f ω ^ 2 + 2 * t * (f ω * g ω)) μ :=
      hf_int.add (hfg_int.const_mul (2 * t))
    have h2 : Integrable (fun ω => t ^ 2 * g ω ^ 2) μ := hg_int.const_mul (t ^ 2)
    have step1 : (fun ω => f ω ^ 2 + 2 * t * (f ω * g ω) + t ^ 2 * g ω ^ 2) =
        (fun ω => (f ω ^ 2 + 2 * t * (f ω * g ω)) + t ^ 2 * g ω ^ 2) := by ext; ring
    rw [step1, integral_add h1 h2]
    have step2 : (fun ω => f ω ^ 2 + 2 * t * (f ω * g ω)) =
        (fun ω => f ω ^ 2 + (2 * t) * (f ω * g ω)) := by ext; ring
    rw [step2, integral_add hf_int (hfg_int.const_mul (2 * t)),
        integral_const_mul, integral_const_mul]
  linarith

/-- Identity expressing the product of the integrals of `min(dP/dQ, 1)` and `max(dP/dQ, 1)`
against `Q` as `1 - TV(P, Q)²`. -/
lemma integral_min_max_rnDeriv_eq {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) :
    (∫ ω, min ((P.rnDeriv Q ω).toReal) 1 ∂Q) *
    (∫ ω, max ((P.rnDeriv Q ω).toReal) 1 ∂Q) =
    1 - tvDist P Q ^ 2 := by
  set f := fun ω => (P.rnDeriv Q ω).toReal with hf_def
  set t := ∫ ω, max (f ω - 1) 0 ∂Q with ht_def
  have hf_int : Integrable f Q := Measure.integrable_toReal_rnDeriv
  have hf1_int : Integrable (fun ω => f ω - 1) Q := hf_int.sub (integrable_const 1)
  have h1f_int : Integrable (fun ω => 1 - f ω) Q := (integrable_const 1).sub hf_int
  have hmax_int : Integrable (fun ω => max (f ω - 1) 0) Q := hf1_int.sup (integrable_const 0)
  have hmax1f_int : Integrable (fun ω => max (1 - f ω) 0) Q := h1f_int.sup (integrable_const 0)
  have hmin_int : Integrable (fun ω => min (f ω) 1) Q := hf_int.inf (integrable_const 1)
  have hmaxf1_int : Integrable (fun ω => max (f ω) 1) Q := hf_int.sup (integrable_const 1)
  have hf_one : ∫ ω, f ω ∂Q = 1 := by
    have := Measure.integral_toReal_rnDeriv hac
    simp [Measure.real, measure_univ] at this; exact this
  have ht_nonneg : 0 ≤ t := integral_nonneg (fun ω => le_max_right _ _)

  have h_neg_eq : ∫ ω, max (1 - f ω) 0 ∂Q = t := by
    have h_pw : ∀ ω, max (f ω - 1) 0 - max (1 - f ω) 0 = f ω - 1 := by
      intro ω; rcases le_or_gt (f ω) 1 with h | h
      · simp [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      · simp [max_eq_left (sub_nonneg.mpr h.le), max_eq_right (sub_nonpos.mpr h.le)]
    have h_congr : ∫ ω, (max (f ω - 1) 0 - max (1 - f ω) 0) ∂Q = ∫ ω, (f ω - 1) ∂Q :=
      integral_congr_ae (Filter.Eventually.of_forall h_pw)
    rw [integral_sub hmax_int hmax1f_int] at h_congr
    have hf1_zero : ∫ ω, (f ω - 1) ∂Q = 0 := by
      rw [integral_sub hf_int (integrable_const 1)]
      simp [integral_const, Measure.real, measure_univ]; linarith
    linarith

  have h_set_fwd : ∀ S : Set Ω, (P S).toReal - (Q S).toReal = ∫ ω in S, (f ω - 1) ∂Q := by
    intro S
    rw [integral_sub hf_int.integrableOn (integrable_const 1).integrableOn]
    have h1 := Measure.setIntegral_toReal_rnDeriv hac S
    simp [Measure.real] at h1; rw [h1]; simp [Measure.real]
  have h_set_rev : ∀ S : Set Ω, (Q S).toReal - (P S).toReal = ∫ ω in S, (1 - f ω) ∂Q := by
    intro S
    rw [integral_sub (integrable_const 1).integrableOn hf_int.integrableOn]
    have h1 := Measure.setIntegral_toReal_rnDeriv hac S
    simp [Measure.real] at h1; rw [h1]; simp [Measure.real]

  have h_bdd : BddAbove {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧
      x = |(P S).toReal - (Q S).toReal|} := by
    use 1; rintro x ⟨S, _, hx⟩; rw [hx]
    have h1 : (P S).toReal ≤ 1 := ENNReal.toReal_mono (by simp) prob_le_one
    have h2 : (Q S).toReal ≤ 1 := ENNReal.toReal_mono (by simp) prob_le_one
    rw [abs_le]; constructor <;>
      linarith [ENNReal.toReal_nonneg (a := P S), ENNReal.toReal_nonneg (a := Q S)]
  have h_ne : Set.Nonempty {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧
      x = |(P S).toReal - (Q S).toReal|} :=
    ⟨0, ∅, MeasurableSet.empty, by simp⟩

  have h_fwd_le : ∀ S : Set Ω, (P S).toReal - (Q S).toReal ≤ t := by
    intro S; rw [h_set_fwd S]
    calc ∫ ω in S, (f ω - 1) ∂Q
        ≤ ∫ ω in S, max (f ω - 1) 0 ∂Q :=
          setIntegral_mono hf1_int.integrableOn hmax_int.integrableOn
            (fun ω => le_max_left _ _)
      _ ≤ ∫ ω, max (f ω - 1) 0 ∂Q :=
          setIntegral_le_integral hmax_int
            (Filter.Eventually.of_forall (fun ω => le_max_right _ _))
  have h_rev_le : ∀ S : Set Ω, (Q S).toReal - (P S).toReal ≤ t := by
    intro S; rw [h_set_rev S]
    calc ∫ ω in S, (1 - f ω) ∂Q
        ≤ ∫ ω in S, max (1 - f ω) 0 ∂Q :=
          setIntegral_mono h1f_int.integrableOn hmax1f_int.integrableOn
            (fun ω => le_max_left _ _)
      _ ≤ ∫ ω, max (1 - f ω) 0 ∂Q :=
          setIntegral_le_integral hmax1f_int
            (Filter.Eventually.of_forall (fun ω => le_max_right _ _))
      _ = t := h_neg_eq

  set A := {ω : Ω | 1 ≤ f ω} with hA_def
  have hA_meas : MeasurableSet A :=
    measurableSet_le measurable_const (Measure.measurable_rnDeriv P Q).ennreal_toReal
  have ht_eq_PA : t = (P A).toReal - (Q A).toReal := by
    show ∫ ω, max (f ω - 1) 0 ∂Q = (P A).toReal - (Q A).toReal
    have h_ind : ∫ ω, max (f ω - 1) 0 ∂Q = ∫ ω in A, (f ω - 1) ∂Q := by
      have h_pw : ∀ ω, max (f ω - 1) 0 = A.indicator (fun ω => f ω - 1) ω := by
        intro ω; simp only [Set.indicator, Set.mem_setOf_eq, A]
        split_ifs with h
        · exact max_eq_left (sub_nonneg.mpr h)
        · simp only [not_le] at h; exact max_eq_right (sub_nonpos.mpr h.le)
      rw [integral_congr_ae (Filter.Eventually.of_forall h_pw), integral_indicator hA_meas]
    rw [h_ind]; exact (h_set_fwd A).symm

  have h_tv : tvDist P Q = t := by
    apply le_antisymm
    · apply csSup_le h_ne
      rintro x ⟨S, _, hx⟩; rw [hx, abs_le]
      exact ⟨by linarith [h_rev_le S], h_fwd_le S⟩
    · rw [ht_eq_PA]
      exact le_trans (le_abs_self _) (le_csSup h_bdd ⟨A, hA_meas, rfl⟩)

  have h_min : ∫ ω, min (f ω) 1 ∂Q = 1 - t := by
    have h_pw : ∀ ω, min (f ω) 1 = f ω - max (f ω - 1) 0 := by
      intro ω; rcases le_or_gt (f ω) 1 with h | h
      · simp [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      · simp [min_eq_right h.le, max_eq_left (sub_nonneg.mpr h.le)]
    rw [integral_congr_ae (Filter.Eventually.of_forall h_pw),
        integral_sub hf_int hmax_int]; linarith

  have h_max : ∫ ω, max (f ω) 1 ∂Q = 1 + t := by
    have h_sum : ∫ ω, min (f ω) 1 ∂Q + ∫ ω, max (f ω) 1 ∂Q = 2 := by
      rw [← integral_add hmin_int hmaxf1_int]
      have h_congr : ∫ ω, (min (f ω) 1 + max (f ω) 1) ∂Q = ∫ ω, (f ω + 1) ∂Q :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => min_add_max (f ω) 1))
      rw [h_congr, integral_add hf_int (integrable_const 1)]
      simp [integral_const, Measure.real, measure_univ]; linarith
    linarith

  rw [h_min, h_max, h_tv]; ring

/-- The squared Bhattacharyya coefficient is bounded above by `1 - TV(P, Q)²`. -/
theorem bc_sq_le_one_sub_tv_sq {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) :
    bhattacharyyaCoeff P Q ^ 2 ≤ 1 - tvDist P Q ^ 2 := by
  unfold bhattacharyyaCoeff

  have h_pw : (fun ω => Real.sqrt (P.rnDeriv Q ω).toReal) =
      (fun ω => Real.sqrt (min ((P.rnDeriv Q ω).toReal) 1) *
                 Real.sqrt (max ((P.rnDeriv Q ω).toReal) 1)) := by
    ext ω
    rw [← Real.sqrt_mul (le_min ENNReal.toReal_nonneg zero_le_one)]
    congr 1
    rcases le_or_gt (P.rnDeriv Q ω).toReal 1 with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h.le, max_eq_left h.le]
  rw [h_pw]

  have h_sq_min : (fun ω => Real.sqrt (min ((P.rnDeriv Q ω).toReal) 1) ^ 2) =
      (fun ω => min ((P.rnDeriv Q ω).toReal) 1) := by
    ext ω; exact sq_sqrt (le_min ENNReal.toReal_nonneg zero_le_one)
  have h_sq_max : (fun ω => Real.sqrt (max ((P.rnDeriv Q ω).toReal) 1) ^ 2) =
      (fun ω => max ((P.rnDeriv Q ω).toReal) 1) := by
    ext ω; exact sq_sqrt (le_max_of_le_right zero_le_one)

  have h_int_f : Integrable (fun ω => (P.rnDeriv Q ω).toReal) Q :=
    Measure.integrable_toReal_rnDeriv
  have h_int_min : Integrable (fun ω => min ((P.rnDeriv Q ω).toReal) 1) Q :=
    h_int_f.mono
      ((Measure.measurable_rnDeriv P Q).ennreal_toReal.min measurable_const).aestronglyMeasurable
      (ae_of_all Q fun ω => by
        simp only [norm_eq_abs]
        rw [abs_of_nonneg (le_min ENNReal.toReal_nonneg zero_le_one),
            abs_of_nonneg ENNReal.toReal_nonneg]
        exact min_le_left _ _)
  have h_int_max : Integrable (fun ω => max ((P.rnDeriv Q ω).toReal) 1) Q :=
    (h_int_f.add (integrable_const 1)).mono
      ((Measure.measurable_rnDeriv P Q).ennreal_toReal.max measurable_const).aestronglyMeasurable
      (ae_of_all Q fun ω => by
        simp only [Pi.add_apply, norm_eq_abs]
        rw [abs_of_nonneg (le_max_of_le_right zero_le_one),
            abs_of_nonneg (by linarith [ENNReal.toReal_nonneg (a := P.rnDeriv Q ω)])]
        exact max_le (le_add_of_nonneg_right zero_le_one)
                     (le_add_of_nonneg_left ENNReal.toReal_nonneg))
  have h_int_sq_min : Integrable
      (fun ω => Real.sqrt (min ((P.rnDeriv Q ω).toReal) 1) ^ 2) Q := by
    rw [h_sq_min]; exact h_int_min
  have h_int_sq_max : Integrable
      (fun ω => Real.sqrt (max ((P.rnDeriv Q ω).toReal) 1) ^ 2) Q := by
    rw [h_sq_max]; exact h_int_max
  have h_int_prod : Integrable (fun ω =>
      Real.sqrt (min ((P.rnDeriv Q ω).toReal) 1) *
      Real.sqrt (max ((P.rnDeriv Q ω).toReal) 1)) Q := by
    rw [← h_pw]
    exact (h_int_f.add (integrable_const 1)).mono
      ((Measure.measurable_rnDeriv P Q).ennreal_toReal.sqrt).aestronglyMeasurable
      (ae_of_all Q fun ω => by
        simp only [norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (by linarith [ENNReal.toReal_nonneg (a := P.rnDeriv Q ω)])]
        have := Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := P.rnDeriv Q ω))
        nlinarith [Real.sqrt_nonneg (P.rnDeriv Q ω).toReal,
                   sq_nonneg (Real.sqrt (P.rnDeriv Q ω).toReal - 1)])

  have h_cs := cauchy_schwarz_integral_sq Q
    (fun ω => Real.sqrt (min ((P.rnDeriv Q ω).toReal) 1))
    (fun ω => Real.sqrt (max ((P.rnDeriv Q ω).toReal) 1))
    (fun ω => Real.sqrt_nonneg _) (fun ω => Real.sqrt_nonneg _)
    h_int_sq_min h_int_sq_max h_int_prod
  rw [h_sq_min, h_sq_max] at h_cs

  rw [← integral_min_max_rnDeriv_eq P Q hac]
  exact h_cs

/-- The Bhattacharyya coefficient is bounded above by `√(1 - TV(P, Q)²)`. -/
theorem bc_le_sqrt_one_sub_tv_sq {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) :
    bhattacharyyaCoeff P Q ≤ Real.sqrt (1 - tvDist P Q ^ 2) := by
  have hbc_nn := bhattacharyyaCoeff_nonneg P Q
  have hsq := bc_sq_le_one_sub_tv_sq P Q hac
  rw [← Real.sqrt_sq hbc_nn]
  exact Real.sqrt_le_sqrt hsq

/-- KL-vs-TV inequality: `KL(P, Q) ≥ 2 - 2·√(1 - TV(P, Q)²)`, obtained by combining
the bounds for KL via Bhattacharyya coefficient and Bhattacharyya coefficient via TV. -/
theorem kl_ge_two_sub_two_sqrt_one_sub_tv_sq {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q)
    (hfin : klDiv P Q ≠ ⊤) :
    klDiv_real P Q ≥ 2 - 2 * Real.sqrt (1 - tvDist P Q ^ 2) := by
  have h1 := kl_ge_two_sub_two_bc P Q hac hfin
  have h2 := bc_le_sqrt_one_sub_tv_sq P Q hac
  linarith

/-- Radon–Nikodym derivative of a product of absolutely continuous measures factors as the
product of the marginal derivatives, almost everywhere with respect to the product reference. -/
theorem rnDeriv_prod_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {P1 Q1 : Measure α} {P2 Q2 : Measure β}
    [SigmaFinite P1] [SigmaFinite Q1]
    [SigmaFinite P2] [SigmaFinite Q2]
    (hac1 : P1.AbsolutelyContinuous Q1)
    (hac2 : P2.AbsolutelyContinuous Q2) :
    (P1.prod P2).rnDeriv (Q1.prod Q2)
      =ᵐ[Q1.prod Q2] fun x => P1.rnDeriv Q1 x.1 * P2.rnDeriv Q2 x.2 := by
  have h1 : Q1.withDensity (P1.rnDeriv Q1) = P1 := Measure.withDensity_rnDeriv_eq P1 Q1 hac1
  have h2 : Q2.withDensity (P2.rnDeriv Q2) = P2 := Measure.withDensity_rnDeriv_eq P2 Q2 hac2
  have h_prod : (Q1.withDensity (P1.rnDeriv Q1)).prod (Q2.withDensity (P2.rnDeriv Q2))
      = (Q1.prod Q2).withDensity (fun z => P1.rnDeriv Q1 z.1 * P2.rnDeriv Q2 z.2) :=
    prod_withDensity₀
      (Measure.measurable_rnDeriv P1 Q1).aemeasurable
      (Measure.measurable_rnDeriv P2 Q2).aemeasurable
  rw [h1, h2] at h_prod
  rw [h_prod]
  exact Measure.rnDeriv_withDensity₀ (Q1.prod Q2)
    (((Measure.measurable_rnDeriv P1 Q1).comp measurable_fst).mul
     ((Measure.measurable_rnDeriv P2 Q2).comp measurable_snd)).aemeasurable

/-- Additivity of KL divergence on product probability measures:
`KL(P₁ ⊗ P₂, Q₁ ⊗ Q₂) = KL(P₁, Q₁) + KL(P₂, Q₂)`. This is part of Proposition 5.6. -/
theorem klDiv_prod_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {P1 Q1 : Measure α} {P2 Q2 : Measure β}
    [IsProbabilityMeasure P1] [IsProbabilityMeasure Q1]
    [IsProbabilityMeasure P2] [IsProbabilityMeasure Q2]
    (hPQ1 : P1.AbsolutelyContinuous Q1) (hPQ2 : P2.AbsolutelyContinuous Q2)
    (h_int1 : Integrable (llr P1 Q1) P1)
    (h_int2 : Integrable (llr P2 Q2) P2) :
    klDiv (P1.prod P2) (Q1.prod Q2) = klDiv P1 Q1 + klDiv P2 Q2 := by

  have hac_prod : (P1.prod P2).AbsolutelyContinuous (Q1.prod Q2) :=
    Measure.AbsolutelyContinuous.prod hPQ1 hPQ2

  haveI : IsProbabilityMeasure (P1.prod P2) := by infer_instance
  haveI : IsProbabilityMeasure (Q1.prod Q2) := by infer_instance

  have h_ae_eq : llr (P1.prod P2) (Q1.prod Q2) =ᵐ[P1.prod P2]
      fun x => llr P1 Q1 x.1 + llr P2 Q2 x.2 := by

    have h_rn := hac_prod.ae_eq (rnDeriv_prod_eq hPQ1 hPQ2)

    have h_pos1 : ∀ᵐ a ∂P1, 0 < P1.rnDeriv Q1 a := Measure.rnDeriv_pos hPQ1
    have h_pos2 : ∀ᵐ b ∂P2, 0 < P2.rnDeriv Q2 b := Measure.rnDeriv_pos hPQ2

    have h_fin1 : ∀ᵐ a ∂P1, P1.rnDeriv Q1 a < ⊤ :=
      hPQ1.ae_le (Measure.rnDeriv_lt_top P1 Q1)
    have h_fin2 : ∀ᵐ b ∂P2, P2.rnDeriv Q2 b < ⊤ :=
      hPQ2.ae_le (Measure.rnDeriv_lt_top P2 Q2)

    have h_ne1 : ∀ᵐ a ∂P1, (P1.rnDeriv Q1 a).toReal ≠ 0 := by
      filter_upwards [h_pos1, h_fin1] with a ha_pos ha_fin
      exact ne_of_gt (ENNReal.toReal_pos (ne_of_gt ha_pos) ha_fin.ne)
    have h_ne2 : ∀ᵐ b ∂P2, (P2.rnDeriv Q2 b).toReal ≠ 0 := by
      filter_upwards [h_pos2, h_fin2] with b hb_pos hb_fin
      exact ne_of_gt (ENNReal.toReal_pos (ne_of_gt hb_pos) hb_fin.ne)

    have h_ne1_prod : ∀ᵐ x ∂(P1.prod P2), (P1.rnDeriv Q1 x.1).toReal ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae h_ne1
    have h_ne2_prod : ∀ᵐ x ∂(P1.prod P2), (P2.rnDeriv Q2 x.2).toReal ≠ 0 :=
      Measure.quasiMeasurePreserving_snd.ae h_ne2

    filter_upwards [h_rn, h_ne1_prod, h_ne2_prod] with x hx_rn hx_ne1 hx_ne2
    simp only [llr]
    rw [hx_rn, ENNReal.toReal_mul, Real.log_mul hx_ne1 hx_ne2]

  have h_int_fst : Integrable (fun x => llr P1 Q1 x.1) (P1.prod P2) := h_int1.comp_fst P2
  have h_int_snd : Integrable (fun x => llr P2 Q2 x.2) (P1.prod P2) := h_int2.comp_snd P1
  have h_int_sum : Integrable (fun x => llr P1 Q1 x.1 + llr P2 Q2 x.2) (P1.prod P2) :=
    h_int_fst.add h_int_snd

  have h_int_prod : Integrable (llr (P1.prod P2) (Q1.prod Q2)) (P1.prod P2) :=
    h_int_sum.congr h_ae_eq.symm

  have hkl1 : klDiv P1 Q1 = ENNReal.ofReal (∫ x, llr P1 Q1 x ∂P1) := by
    rw [klDiv_of_ac_of_integrable hPQ1 h_int1]; congr 1
    simp [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  have hkl2 : klDiv P2 Q2 = ENNReal.ofReal (∫ x, llr P2 Q2 x ∂P2) := by
    rw [klDiv_of_ac_of_integrable hPQ2 h_int2]; congr 1
    simp [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  have hkl_prod : klDiv (P1.prod P2) (Q1.prod Q2) =
      ENNReal.ofReal (∫ x, llr (P1.prod P2) (Q1.prod Q2) x ∂(P1.prod P2)) := by
    rw [klDiv_of_ac_of_integrable hac_prod h_int_prod]; congr 1
    simp [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]

  have h_decomp : ∫ x, llr (P1.prod P2) (Q1.prod Q2) x ∂(P1.prod P2) =
      ∫ x, llr P1 Q1 x ∂P1 + ∫ x, llr P2 Q2 x ∂P2 := by
    rw [show ∫ x, llr (P1.prod P2) (Q1.prod Q2) x ∂(P1.prod P2) =
        ∫ x, (llr P1 Q1 x.1 + llr P2 Q2 x.2) ∂(P1.prod P2) from integral_congr_ae h_ae_eq,
      integral_add h_int_fst h_int_snd]
    congr 1
    · rw [integral_prod _ h_int_fst]
      simp_rw [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
        ENNReal.toReal_one, one_smul]
    · rw [integral_prod_symm _ h_int_snd]
      simp_rw [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
        ENNReal.toReal_one, one_smul]

  have h1_nn : 0 ≤ ∫ x, llr P1 Q1 x ∂P1 := by
    have := integral_llr_add_sub_measure_univ_nonneg hPQ1 h_int1
    simp [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one] at this
    linarith
  have h2_nn : 0 ≤ ∫ x, llr P2 Q2 x ∂P2 := by
    have := integral_llr_add_sub_measure_univ_nonneg hPQ2 h_int2
    simp [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one] at this
    linarith

  rw [hkl_prod, hkl1, hkl2, h_decomp, ENNReal.ofReal_add h1_nn h2_nn]

/-- Uniform mixture measure `(1/M) ∑ⱼ Pⱼ` of a finite family of probability measures. -/
noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin M → Measure Ω) : Measure Ω :=
  (1 / (M : ENNReal)) • Finset.sum Finset.univ (fun j => P j)

/-- Pointwise entropy bound used in Fano's inequality: for a probability vector `p` on
`Fin M` with `M ≥ 2`, `∑ⱼ -pⱼ log pⱼ ≤ log 2 + (1 - p_max) · log(M - 1)`. -/
theorem fano_pointwise_entropy_bound (M : ℕ) (hM : 2 ≤ M)
    (p : Fin M → ℝ)
    (hp_nn : ∀ j, 0 ≤ p j)
    (hp_sum : ∑ j, p j = 1)
    (i_max : Fin M) :
    ∑ j, negMulLog (p j) ≤
      Real.log 2 + (1 - p i_max) * Real.log ((M : ℝ) - 1) := by

  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := Nat.ofNat_le_cast.mpr hM; linarith
  have hM1_ne : ((M : ℝ) - 1) ≠ 0 := ne_of_gt hM1
  set s := 1 - p i_max with hs_def
  have hp_max_le1 : p i_max ≤ 1 := by
    calc p i_max ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp_nn j) (Finset.mem_univ _)
    _ = 1 := hp_sum
  have hs_nn : 0 ≤ s := by linarith

  have hsum_split : ∑ j, negMulLog (p j) =
      negMulLog (p i_max) + ∑ j ∈ Finset.univ.erase i_max, negMulLog (p j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i_max)]
  rw [hsum_split]

  have jensen : ∑ j ∈ Finset.univ.erase i_max, (1 / ((M : ℝ) - 1)) • negMulLog (p j) ≤
      negMulLog (∑ j ∈ Finset.univ.erase i_max, (1 / ((M : ℝ) - 1)) • p j) := by
    apply ConcaveOn.le_map_sum concaveOn_negMulLog
    · intro j _; exact div_nonneg one_pos.le hM1.le
    · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one, one_div, mul_inv_cancel₀ hM1_ne]
    · intro j _; exact Set.mem_Ici.mpr (hp_nn j)

  have hws : ∑ j ∈ Finset.univ.erase i_max, (1 / ((M : ℝ) - 1)) • negMulLog (p j) =
      (1 / ((M : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i_max, negMulLog (p j) := by
    rw [← Finset.smul_sum]; rfl

  have hwp : ∑ j ∈ Finset.univ.erase i_max, (1 / ((M : ℝ) - 1)) • p j =
      s / ((M : ℝ) - 1) := by
    rw [← Finset.smul_sum]
    simp only [smul_eq_mul, one_div, inv_mul_eq_div]
    congr 1
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hp_sum]
  rw [hws, hwp] at jensen

  have hrest : ∑ j ∈ Finset.univ.erase i_max, negMulLog (p j) ≤
      ((M : ℝ) - 1) * negMulLog (s / ((M : ℝ) - 1)) := by
    have := mul_le_mul_of_nonneg_left jensen hM1.le
    rwa [← mul_assoc, mul_one_div_cancel hM1_ne, one_mul] at this

  have hexpand : ((M : ℝ) - 1) * negMulLog (s / ((M : ℝ) - 1)) =
      negMulLog s + s * Real.log ((M : ℝ) - 1) := by
    simp only [negMulLog, neg_mul]
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [Real.log_div hs0 hM1_ne]; field_simp; ring
  rw [hexpand] at hrest

  have hbin : negMulLog (p i_max) + negMulLog s = binEntropy (p i_max) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  calc negMulLog (p i_max) + ∑ j ∈ Finset.univ.erase i_max, negMulLog (p j)
      ≤ negMulLog (p i_max) + (negMulLog s + s * Real.log ((M : ℝ) - 1)) := by linarith
    _ = (negMulLog (p i_max) + negMulLog s) + s * Real.log ((M : ℝ) - 1) := by ring
    _ = binEntropy (p i_max) + s * Real.log ((M : ℝ) - 1) := by rw [hbin]
    _ ≤ Real.log 2 + s * Real.log ((M : ℝ) - 1) := by
        linarith [binEntropy_le_log_two (p := p i_max)]

/-- The posterior entropy of a measurable test `ψ` under each `P_j` is bounded by
`log 2 + P_j(ψ ≠ j) · log(M - 1)`, a measure-theoretic consequence of `fano_pointwise_entropy_bound`. -/
theorem posterior_entropy_le_error_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (ψ : Ω → Fin M) (hψ : Measurable ψ) (j : Fin M) :
    ∑ k : Fin M, negMulLog ((P j {ω | ψ ω = k}).toReal) ≤
      Real.log 2 + (P j {ω | ψ ω ≠ j}).toReal * Real.log ((M : ℝ) - 1) := by

  set p : Fin M → ℝ := fun k => (P j {ω | ψ ω = k}).toReal with hp_def
  have hp_nn : ∀ k, 0 ≤ p k := fun k => ENNReal.toReal_nonneg

  have hMeas : ∀ k : Fin M, MeasurableSet {ω | ψ ω = k} :=
    fun k => hψ (measurableSet_singleton k)

  have hDisjoint : ∀ i j' : Fin M, i ≠ j' →
      Disjoint ({ω | ψ ω = i} : Set Ω) {ω | ψ ω = j'} := by
    intro i j' hij; exact Set.disjoint_left.mpr fun ω hi hj' => hij (hi.symm.trans hj')

  have hUnion : ⋃ k : Fin M, {ω | ψ ω = k} = Set.univ := by
    ext ω; simp [Set.mem_iUnion]

  have hp_sum : ∑ k, p k = 1 := by
    simp only [hp_def]
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top (P j) _)]
    have : ∑ k : Fin M, P j {ω | ψ ω = k} =
        P j (⋃ k ∈ Finset.univ, {ω | ψ ω = k}) :=
      (measure_biUnion_finset (fun i _ j' _ hij => hDisjoint i j' hij)
        (fun k _ => hMeas k)).symm
    rw [this]
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [hUnion, measure_univ, ENNReal.toReal_one]

  have hFano := fano_pointwise_entropy_bound M hM p hp_nn hp_sum j

  have hcompl : 1 - p j = (P j {ω | ψ ω ≠ j}).toReal := by
    simp only [hp_def]
    have hMeasJ : MeasurableSet {ω | ψ ω = j} := hMeas j
    have hc : {ω | ψ ω ≠ j} = {ω | ψ ω = j}ᶜ := by ext; simp
    rw [hc, measure_compl hMeasJ (measure_ne_top (P j) _)]
    rw [ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top (P j) _)]
    simp [measure_univ, ENNReal.toReal_one]
  rw [hcompl] at hFano
  exact hFano


/-- Restriction commutes with the Radon–Nikodym derivative: the derivative of the restricted
measures equals the original derivative, almost everywhere on `s`. -/
lemma rnDeriv_restrict_ae_eq_kl {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [SigmaFinite ν] [μ.HaveLebesgueDecomposition ν]
    (hac : μ ≪ ν) {s : Set Ω} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
  rw [show μ.restrict s = (ν.restrict s).withDensity (μ.rnDeriv ν) from by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hac]; exact restrict_withDensity hs _]
  exact Measure.rnDeriv_withDensity (ν.restrict s) (Measure.measurable_rnDeriv μ ν)


/-- The KL divergence of the restricted measures equals the set lintegral of `klFun (dμ/dν)`
over `s` with respect to `ν`. -/
lemma klDiv_restrict_eq_set_lintegral_kl {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {s : Set Ω} (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) =
      ∫⁻ x in s, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.restrict s)]
  apply lintegral_congr_ae
  filter_upwards [rnDeriv_restrict_ae_eq_kl hac hs] with x hx; rw [hx]


/-- Monotonicity of KL divergence under restriction: `KL(μ|_s, ν|_s) ≤ KL(μ, ν)`. -/
theorem klDiv_restrict_le_kl {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {s : Set Ω} (hs : MeasurableSet s) :
    klDiv (μ.restrict s) (ν.restrict s) ≤ klDiv μ ν := by
  rw [klDiv_restrict_eq_set_lintegral_kl hac hs, klDiv_eq_lintegral_klFun_of_ac hac]
  exact setLIntegral_le_lintegral s _


/-- Decomposition of KL divergence over a finite measurable partition induced by `ψ`:
the sum of the cellwise KL divergences equals the global KL divergence. -/
lemma klDiv_eq_sum_restrict_kl {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {M : ℕ} (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ∑ k : Fin M, klDiv (μ.restrict (ψ ⁻¹' {k})) (ν.restrict (ψ ⁻¹' {k})) = klDiv μ ν := by
  have hmeas : ∀ k : Fin M, MeasurableSet (ψ ⁻¹' {k}) := fun k => hψ (measurableSet_singleton k)
  let f : Ω → ENNReal := fun x => ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal)
  suffices h : ∑' k : Fin M, ∫⁻ x in ψ ⁻¹' {k}, f x ∂ν = ∫⁻ x, f x ∂ν by
    simp_rw [klDiv_restrict_eq_set_lintegral_kl hac (hmeas _)]
    rw [show ∑ k : Fin M, ∫⁻ x in ψ ⁻¹' {k}, f x ∂ν =
        ∑' k : Fin M, ∫⁻ x in ψ ⁻¹' {k}, f x ∂ν from (tsum_fintype _).symm]
    rw [h, klDiv_eq_lintegral_klFun_of_ac hac]
  rw [← lintegral_iUnion hmeas (by
    intro i j hij; simp only [Set.disjoint_left]
    intro x hi hj; simp at hi hj; exact hij (hi ▸ hj ▸ rfl))]
  rw [show (⋃ k : Fin M, ψ ⁻¹' {k}) = Set.univ from by ext x; simp]
  rw [Measure.restrict_univ]


/-- For a probability measure `μ` and measurable `ψ : Ω → Fin M`, the cell probabilities
`μ(ψ⁻¹{k})` sum to one. -/
lemma partition_sum_eq_one_kl {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {M : ℕ} (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ∑ k : Fin M, (μ (ψ ⁻¹' {k})).toReal = 1 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun k : Fin M => ψ ⁻¹' {k}) := by
    intro i j hij; simp only [Function.onFun, Set.disjoint_left]
    intro x hi hj; simp at hi hj; exact hij (hi ▸ hj ▸ rfl)
  have hmeas : ∀ k : Fin M, MeasurableSet (ψ ⁻¹' {k}) := fun k => hψ (measurableSet_singleton k)
  rw [show (1 : ℝ) = (1 : ENNReal).toReal from by simp,
    show (1 : ENNReal) = μ (⋃ k : Fin M, ψ ⁻¹' {k}) from by
      rw [show (⋃ k : Fin M, ψ ⁻¹' {k}) = Set.univ from by ext x; simp]; exact measure_univ.symm,
    measure_iUnion hdisj hmeas,
    ENNReal.tsum_toReal_eq (fun k => ne_top_of_le_ne_top (measure_ne_top μ _) le_rfl)]
  simp [tsum_fintype]

/-- Data-processing inequality for KL divergence via a measurable partition: the discrete KL
divergence between the pushforwards `μ ∘ ψ⁻¹` and `ν ∘ ψ⁻¹` lower bounds `KL(μ, ν)`. -/
theorem klDiv_ge_partition_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hfin : klDiv μ ν ≠ ⊤)
    (M : ℕ) (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    (klDiv μ ν).toReal ≥ ∑ k : Fin M,
      (μ (ψ ⁻¹' {↑k})).toReal * Real.log ((μ (ψ ⁻¹' {↑k})).toReal / (ν (ψ ⁻¹' {↑k})).toReal) := by
  have hm_k : ∀ k : Fin M, MeasurableSet (ψ ⁻¹' {k}) := fun k => hψ (measurableSet_singleton k)

  have cell_bound : ∀ k : Fin M,
      (μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
        + (ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal
      ≤ (klDiv (μ.restrict (ψ ⁻¹' {k})) (ν.restrict (ψ ⁻¹' {k}))).toReal := by
    intro k
    have hkl_ne : klDiv (μ.restrict (ψ ⁻¹' {k})) (ν.restrict (ψ ⁻¹' {k})) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (klDiv_restrict_le_kl hac (hm_k k))
    have ⟨hac_k, hint_k⟩ := klDiv_ne_top_iff.mp hkl_ne
    convert mul_log_le_toReal_klDiv hac_k hint_k using 2 <;> simp [Measure.real]

  suffices h : ∑ k : Fin M,
      ((μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
        + (ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal)
      ≤ (klDiv μ ν).toReal by

    have hsimp : ∑ k : Fin M,
        ((μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
          + (ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal) =
        ∑ k : Fin M, (μ (ψ ⁻¹' {k})).toReal *
          Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal) := by
      simp_rw [show ∀ k : Fin M,
        (μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
          + (ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal =
        (μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
          + ((ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal) from fun k => by ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        partition_sum_eq_one_kl ν ψ hψ, partition_sum_eq_one_kl μ ψ hψ, sub_self, add_zero]
    linarith [hsimp ▸ h]

  calc ∑ k : Fin M,
        ((μ (ψ ⁻¹' {k})).toReal * Real.log ((μ (ψ ⁻¹' {k})).toReal / (ν (ψ ⁻¹' {k})).toReal)
          + (ν (ψ ⁻¹' {k})).toReal - (μ (ψ ⁻¹' {k})).toReal)
      ≤ ∑ k : Fin M, (klDiv (μ.restrict (ψ ⁻¹' {k})) (ν.restrict (ψ ⁻¹' {k}))).toReal :=
        Finset.sum_le_sum (fun k _ => cell_bound k)
    _ ≤ (∑ k : Fin M, klDiv (μ.restrict (ψ ⁻¹' {k})) (ν.restrict (ψ ⁻¹' {k}))).toReal := by
        rw [ENNReal.toReal_sum
          (fun k _ => ne_top_of_le_ne_top hfin (klDiv_restrict_le_kl hac (hm_k k)))]
    _ = (klDiv μ ν).toReal := by rw [klDiv_eq_sum_restrict_kl hac ψ hψ]

/-- Pointwise upper bound `klFun x ≤ (x - 1)²` for `x ≥ 0`. -/
lemma klFun_le_sq_sub (x : ℝ) (hx : 0 ≤ x) : klFun x ≤ (x - 1) ^ 2 := by
  unfold klFun
  have h : x * Real.log x ≤ x * (x - 1) := by
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx_pos) hx_pos.le
  nlinarith

set_option maxHeartbeats 4000000 in
/-- When the pairwise KL divergences are finite, the KL divergence of any `P_j` against the
uniform mixture is also finite. -/
theorem klDiv_mixture_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (_hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (_hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤)
    (j : Fin M) :
    klDiv (P j) (mixtureMeasure M P) ≠ ⊤ := by
  have hM_pos : 0 < M := by omega
  have hM_ennreal_ne : (M : ENNReal) ≠ 0 := by exact_mod_cast hM_pos.ne'
  have hM_ne_top : (M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top M
  have h1M_ne : (1 / (M : ENNReal)) ≠ 0 := by
    rw [one_div]; exact ENNReal.inv_ne_zero.mpr hM_ne_top

  set S : Measure Ω := Finset.sum Finset.univ P with hS_def

  haveI hS_fin : IsFiniteMeasure S := by
    constructor
    simp only [hS_def, Measure.coe_finset_sum, Finset.sum_apply, measure_univ, Finset.sum_const,
               Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact hM_ne_top.lt_top

  haveI : IsProbabilityMeasure (mixtureMeasure M P) := by
    constructor
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
               Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
               Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [one_div, ENNReal.inv_mul_cancel hM_ennreal_ne hM_ne_top]

  have hac_mix : P j ≪ mixtureMeasure M P := by
    intro s hs
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
               Finset.sum_apply] at hs
    have h_sum_zero : ∑ k : Fin M, P k s = 0 := by
      by_contra hne; exact absurd hs (mul_ne_zero h1M_ne hne)
    exact Finset.sum_eq_zero_iff.mp h_sum_zero j (Finset.mem_univ j)

  rw [klDiv_eq_lintegral_klFun, if_pos hac_mix]

  have hle : P j ≤ S := by
    intro s
    simp only [hS_def, Measure.coe_finset_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun k => P k s) (fun _ _ => zero_le _) (Finset.mem_univ j)
  have h_rn_S_le : (P j).rnDeriv S ≤ᵐ[S] 1 := Measure.rnDeriv_le_one_of_le hle

  have h1M_ne_top : (1 / (M : ENNReal)) ≠ ⊤ := by
    rw [one_div]; exact ENNReal.inv_ne_top.mpr hM_ennreal_ne
  have h_smul_ae : (P j).rnDeriv ((1 / (M : ENNReal)) • S) =ᵐ[S]
      (1 / (M : ENNReal))⁻¹ • (P j).rnDeriv S :=
    Measure.rnDeriv_smul_right_of_ne_top (P j) S h1M_ne h1M_ne_top

  have h_rn_le_M_S : ∀ᵐ x ∂S, (P j).rnDeriv (mixtureMeasure M P) x ≤ (M : ENNReal) := by
    filter_upwards [h_smul_ae, h_rn_S_le] with x hx_eq hx_le
    show (P j).rnDeriv ((1 / (M : ENNReal)) • S) x ≤ (M : ENNReal)
    rw [hx_eq]
    simp only [Pi.smul_apply, smul_eq_mul, one_div, inv_inv]
    exact (mul_le_mul_of_nonneg_left hx_le (zero_le _)).trans_eq (mul_one _)

  have h_rn_le_M : ∀ᵐ x ∂(mixtureMeasure M P),
      (P j).rnDeriv (mixtureMeasure M P) x ≤ (M : ENNReal) := by
    show ∀ᵐ x ∂((1 / (M : ENNReal)) • S), _
    exact Measure.ae_smul_measure h_rn_le_M_S _

  set C := ENNReal.ofReal (((M : ℝ) - 1) ^ 2) with hC_def
  have h_bound : ∀ᵐ x ∂(mixtureMeasure M P),
      ENNReal.ofReal (klFun ((P j).rnDeriv (mixtureMeasure M P) x).toReal) ≤ C := by
    filter_upwards [h_rn_le_M, Measure.rnDeriv_lt_top (P j) (mixtureMeasure M P)]
      with x hx_le hx_lt
    apply ENNReal.ofReal_le_ofReal
    have h_nn : 0 ≤ ((P j).rnDeriv (mixtureMeasure M P) x).toReal := ENNReal.toReal_nonneg
    have h_le_M : ((P j).rnDeriv (mixtureMeasure M P) x).toReal ≤ M := by
      rw [← ENNReal.toReal_natCast (n := M)]
      exact (ENNReal.toReal_le_toReal hx_lt.ne hM_ne_top).mpr hx_le
    calc klFun ((P j).rnDeriv (mixtureMeasure M P) x).toReal
        ≤ (((P j).rnDeriv (mixtureMeasure M P) x).toReal - 1) ^ 2 := klFun_le_sq_sub _ h_nn
      _ ≤ ((M : ℝ) - 1) ^ 2 := by
          have : (1 : ℝ) ≤ (M : ℝ) - 1 := by
            have : (2 : ℝ) ≤ M := Nat.ofNat_le_cast.mpr _hM; linarith
          exact sq_le_sq' (by linarith) (by linarith)

  have h_lint_le : ∫⁻ x,
      ENNReal.ofReal (klFun ((P j).rnDeriv (mixtureMeasure M P) x).toReal)
      ∂(mixtureMeasure M P) ≤ ∫⁻ _, C ∂(mixtureMeasure M P) := lintegral_mono_ae h_bound
  rw [lintegral_const, measure_univ, mul_one] at h_lint_le
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_lint_le

/-- Algebraic identity expressing the term `b · (-x log x)` with `x = a/(M·b)` in a form
suitable for the data-processing argument used in Fano's inequality. -/
lemma negMulLog_term_identity_dpi
    (a b : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) :
    b * negMulLog (a / (↑M * b)) =
    -(1 / ↑M) * a * Real.log (a / b) + a * Real.log ↑M / ↑M := by
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
  by_cases hb0 : b = 0
  · simp [hb0, hab hb0]
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases ha0 : a = 0
  · simp [ha0, negMulLog_zero]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  simp only [negMulLog, neg_mul]
  rw [Real.log_div (ne_of_gt ha_pos) (ne_of_gt (mul_pos hM_pos hb_pos))]
  rw [Real.log_mul (ne_of_gt hM_pos) (ne_of_gt hb_pos)]
  rw [Real.log_div (ne_of_gt ha_pos) (ne_of_gt hb_pos)]
  ring_nf; field_simp

/-- Discrete algebraic identity relating the average pairwise KL term to the entropy of the
posterior mixture, used to derive the data-processing form of Fano's inequality. -/
lemma algebraic_identity_for_dpi
    (M : ℕ) (hM : 2 ≤ M)
    (a : Fin M → Fin M → ℝ) (b : Fin M → ℝ)
    (ha : ∀ j k, 0 ≤ a j k) (hb : ∀ k, 0 ≤ b k)
    (hab : ∀ j k, b k = 0 → a j k = 0)
    (prob_sum : ∀ j, ∑ k, a j k = 1)
    (_sum_b : ∑ k, b k = 1) :
    Real.log ↑M - 1 / ↑M * ∑ j, ∑ k, a j k * Real.log (a j k / b k) =
    ∑ k, b k * ∑ j, negMulLog (a j k / (↑M * b k)) := by
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
  have hM_ne : (↑M : ℝ) ≠ 0 := ne_of_gt hM_pos
  suffices h : ∑ k, b k * ∑ j, negMulLog (a j k / (↑M * b k)) =
      -(1 / ↑M * ∑ j, ∑ k, a j k * Real.log (a j k / b k)) + Real.log ↑M by linarith
  have step1 : ∀ k, b k * ∑ j, negMulLog (a j k / (↑M * b k)) =
      ∑ j, (-(1 / ↑M) * a j k * Real.log (a j k / b k) + a j k * Real.log ↑M / ↑M) := by
    intro k; rw [Finset.mul_sum]; congr 1; ext j
    exact negMulLog_term_identity_dpi (a j k) (b k) M hM (ha j k) (hb k) (hab j k)
  simp_rw [step1]
  trans (∑ k, ∑ j, -(1 / ↑M) * a j k * Real.log (a j k / b k)) +
       (∑ k, ∑ j, a j k * Real.log ↑M / ↑M)
  · rw [← Finset.sum_add_distrib]; congr 1; ext k; exact Finset.sum_add_distrib
  congr 1
  · rw [Finset.sum_comm]
    simp_rw [show ∀ j k, -(1 / (↑M : ℝ)) * a j k * Real.log (a j k / b k) =
        -(1 / ↑M) * (a j k * Real.log (a j k / b k)) from fun j k => by ring]
    rw [show -(1 / ↑M * ∑ j, ∑ k, a j k * Real.log (a j k / b k)) =
        ∑ j, (-(1 / ↑M) * ∑ k, a j k * Real.log (a j k / b k)) from by
      rw [Finset.mul_sum]; simp_rw [neg_mul, Finset.sum_neg_distrib]]
    congr 1; ext j; rw [← Finset.mul_sum]
  · rw [Finset.sum_comm]
    have : ∀ j : Fin M, ∑ k, a j k * Real.log ↑M / ↑M = Real.log ↑M / ↑M := by
      intro j; rw [← Finset.sum_div, ← Finset.sum_mul, prob_sum j, one_mul]
    simp_rw [this, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp

/-- Variant of `partition_sum_eq_one_kl`: the cell probabilities of a measurable partition of
a probability measure sum to one. -/
lemma partition_sum_eq_one_dpi {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ) (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ∑ k : Fin M, (μ (ψ ⁻¹' {↑k})).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top μ _)]
  have key : ∑ k : Fin M, μ (ψ ⁻¹' {↑k}) = 1 := by
    rw [← measure_univ (μ := μ)]
    rw [← measure_biUnion_finset]
    · congr 1; ext ω; constructor
      · intro _; exact Set.mem_univ _
      · intro _
        simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨ψ ω, trivial, rfl⟩
    · intro i _ j _ hij
      exact Set.disjoint_left.mpr fun ω hi hj =>
        hij (by simpa using (hi : ψ ω = ↑i).symm.trans (hj : ψ ω = ↑j))
    · intro k _; exact hψ (measurableSet_singleton _)
  rw [key]; simp

/-- Data-processing inequality for KL divergence against the uniform mixture:
`log M - avg_j KL(P_j, P̄) ≤ posterior entropy of the partition induced by ψ`. -/
theorem data_processing_kl_partition
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    Real.log (M : ℝ) - (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
    ∑ k : Fin M, (mixtureMeasure M P (ψ ⁻¹' {↑k})).toReal *
      ∑ j : Fin M, negMulLog ((P j (ψ ⁻¹' {↑k})).toReal /
        ((M : ℝ) * (mixtureMeasure M P (ψ ⁻¹' {↑k})).toReal)) := by
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
  have hM_ne : (↑M : ℝ) ≠ 0 := ne_of_gt hM_pos

  set a : Fin M → Fin M → ℝ := fun j k => (P j (ψ ⁻¹' {↑k})).toReal with ha_def
  set b : Fin M → ℝ := fun k => (mixtureMeasure M P (ψ ⁻¹' {↑k})).toReal with hb_def

  have hac : ∀ j, P j ≪ mixtureMeasure M P := by
    intro j s hs
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul] at hs
    have h1M : (1 : ENNReal) / (M : ENNReal) ≠ 0 := by
      rw [one_div]; exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
    have := (mul_eq_zero.mp hs).resolve_left h1M
    rw [Measure.finset_sum_apply] at this
    exact Finset.sum_eq_zero_iff.mp this j (Finset.mem_univ j)

  have ha_nn : ∀ j k, 0 ≤ a j k := fun j k => ENNReal.toReal_nonneg
  have hb_nn : ∀ k, 0 ≤ b k := fun k => ENNReal.toReal_nonneg
  haveI : IsProbabilityMeasure (mixtureMeasure M P) := by
    constructor
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
               Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
               Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [one_div, ENNReal.inv_mul_cancel]
    · exact_mod_cast (show 0 < M by omega).ne'
    · exact ENNReal.natCast_ne_top M
  have hab : ∀ j k, b k = 0 → a j k = 0 := by
    intro j k hbk
    simp only [ha_def, hb_def] at *
    have hmix_zero : mixtureMeasure M P (ψ ⁻¹' {↑k}) = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hbk).resolve_right (measure_ne_top _ _)
    have := hac j hmix_zero
    exact (ENNReal.toReal_eq_zero_iff _).mpr (Or.inl this)
  have prob_sum : ∀ j, ∑ k, a j k = 1 :=
    fun j => partition_sum_eq_one_dpi (P j) M ψ hψ
  have sum_b : ∑ k, b k = 1 :=
    partition_sum_eq_one_dpi (mixtureMeasure M P) M ψ hψ

  have alg_id := algebraic_identity_for_dpi M hM a b ha_nn hb_nn hab prob_sum sum_b

  have dpi : ∀ j, (klDiv (P j) (mixtureMeasure M P)).toReal ≥
      ∑ k, a j k * Real.log (a j k / b k) := by
    intro j
    exact klDiv_ge_partition_sum (P j) (mixtureMeasure M P) (hac j) (hfin_kl j) M ψ hψ

  rw [← alg_id]
  apply sub_le_sub_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun j _ => dpi j)

/-- Weighted averaging of pointwise Fano-type bounds: a convex combination of bounds of the
form `h_k ≤ log 2 + e_k · log(M-1)` yields the same bound for the averaged quantities. -/
lemma weighted_fano_bound {M : ℕ}
    (w : Fin M → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (h : Fin M → ℝ) (e : Fin M → ℝ)
    (hbound : ∀ k, h k ≤ Real.log 2 + e k * Real.log ((M : ℝ) - 1)) :
    ∑ k, w k * h k ≤ Real.log 2 + (∑ k, w k * e k) * Real.log ((M : ℝ) - 1) := by
  have key : ∑ k, w k * h k ≤
      ∑ k, (w k * Real.log 2 + w k * e k * Real.log ((M : ℝ) - 1)) := by
    apply Finset.sum_le_sum
    intro k _
    have := mul_le_mul_of_nonneg_left (hbound k) (hw_nn k)
    linarith [mul_add (w k) (Real.log 2) (e k * Real.log ((M : ℝ) - 1)),
              mul_mul_mul_comm (w k) (e k) (Real.log ((M : ℝ) - 1))]
  have rhs_eq : ∑ k, (w k * Real.log 2 + w k * e k * Real.log ((M : ℝ) - 1)) =
      Real.log 2 + (∑ k, w k * e k) * Real.log ((M : ℝ) - 1) := by
    rw [Finset.sum_add_distrib,
      show ∑ x, w x * Real.log 2 = (∑ x, w x) * Real.log 2 from by rw [← Finset.sum_mul],
      show ∑ x, w x * e x * Real.log ((M : ℝ) - 1) = (∑ x, w x * e x) * Real.log ((M : ℝ) - 1)
        from by rw [← Finset.sum_mul],
      hw_sum, one_mul]
  linarith

/-- Fano-style upper bound on the conditional entropy of the partition induced by `ψ` under
the mixture, in terms of the average error probability `(1/M) ∑_j P_j(ψ ≠ j)`. -/
theorem cond_entropy_fano_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ∑ k : Fin M, (mixtureMeasure M P (ψ ⁻¹' {↑k})).toReal *
      ∑ j : Fin M, negMulLog ((P j (ψ ⁻¹' {↑k})).toReal /
        ((M : ℝ) * (mixtureMeasure M P (ψ ⁻¹' {↑k})).toReal)) ≤
    Real.log 2 + ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) *
      Real.log ((M : ℝ) - 1) := by

  have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
  set w : Fin M → ℝ := fun k => (mixtureMeasure M P (ψ ⁻¹' {k})).toReal with hw_def

  have hMeas : ∀ k : Fin M, MeasurableSet (ψ ⁻¹' {k}) :=
    fun k => hψ (measurableSet_singleton k)

  have hDisjoint : ∀ i j : Fin M, i ≠ j →
      Disjoint (ψ ⁻¹' {i} : Set Ω) (ψ ⁻¹' {j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun ω hi hj => hij (by simpa using hi.symm.trans hj)

  have hUnion : ⋃ k : Fin M, ψ ⁻¹' {k} = Set.univ := by
    ext ω; simp [Set.mem_iUnion, Set.mem_preimage]

  have hM_pos_nat : 0 < M := by omega
  haveI h_mix_prob : IsProbabilityMeasure (mixtureMeasure M P) := by
    constructor
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
               Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
               Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [one_div, ENNReal.inv_mul_cancel]
    · exact_mod_cast hM_pos_nat.ne'
    · exact ENNReal.natCast_ne_top M

  have hw_sum : ∑ k, w k = 1 := by
    simp only [hw_def]
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top (mixtureMeasure M P) _)]
    have : ∑ k : Fin M, mixtureMeasure M P (ψ ⁻¹' {k}) =
        mixtureMeasure M P (⋃ k ∈ Finset.univ, ψ ⁻¹' {k}) := by
      rw [measure_biUnion_finset
        (fun i hi j' hj' hij => hDisjoint i j' hij) (fun k _ => hMeas k)]
    rw [this]
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [hUnion, measure_univ, ENNReal.toReal_one]

  have hw_nn : ∀ k, 0 ≤ w k := fun k => ENNReal.toReal_nonneg

  set h_fn : Fin M → ℝ := fun k => ∑ j : Fin M,
    negMulLog ((P j (ψ ⁻¹' {k})).toReal / ((M : ℝ) * w k)) with hh_def
  set e_fn : Fin M → ℝ := fun k =>
    1 - (P k (ψ ⁻¹' {k})).toReal / ((M : ℝ) * w k) with he_def

  have hLHS : ∑ k : Fin M, w k * h_fn k =
      ∑ k : Fin M, (mixtureMeasure M P (ψ ⁻¹' {k})).toReal *
        ∑ j : Fin M, negMulLog ((P j (ψ ⁻¹' {k})).toReal /
          ((M : ℝ) * (mixtureMeasure M P (ψ ⁻¹' {k})).toReal)) := by
    rfl

  have hPj_zero_of_w_zero : ∀ k, w k = 0 → ∀ j, P j (ψ ⁻¹' {k}) = 0 := by
    intro k hw0 j
    simp only [hw_def, mixtureMeasure, Measure.smul_apply, smul_eq_mul,
               Measure.coe_finset_sum, Finset.sum_apply] at hw0
    rw [ENNReal.toReal_eq_zero_iff] at hw0
    cases hw0 with
    | inl h0 =>
      have h1div_ne : (1 / (M : ENNReal)) ≠ 0 := by
        simp only [one_div]
        exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
      have hsum0 := (mul_eq_zero.mp h0).resolve_left h1div_ne
      exact Finset.sum_eq_zero_iff.mp hsum0 j (Finset.mem_univ j)
    | inr htop =>
      exfalso
      have : (1 / (M : ENNReal)) * ∑ i, P i (ψ ⁻¹' {k}) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · exact ENNReal.div_ne_top ENNReal.one_ne_top (by exact_mod_cast hM_pos_nat.ne')
        · exact ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top _ _
      exact this htop

  have hbound : ∀ k, h_fn k ≤ Real.log 2 + e_fn k * Real.log ((M : ℝ) - 1) := by
    intro k

    set post : Fin M → ℝ := fun j => (P j (ψ ⁻¹' {k})).toReal / ((M : ℝ) * w k) with hpost_def

    change ∑ j, negMulLog (post j) ≤ Real.log 2 + (1 - post k) * Real.log ((M : ℝ) - 1)

    have hpost_nn : ∀ j, 0 ≤ post j := by
      intro j; simp only [hpost_def]
      apply div_nonneg ENNReal.toReal_nonneg
      apply mul_nonneg (Nat.cast_nonneg M) ENNReal.toReal_nonneg
    by_cases hw0 : w k = 0
    ·
      have hpost_zero : ∀ j, post j = 0 := by
        intro j
        simp only [hpost_def]
        have : (P j (ψ ⁻¹' {k})).toReal = 0 := by
          have := hPj_zero_of_w_zero k hw0 j
          simp [this]
        rw [this, zero_div]
      simp only [hpost_zero, negMulLog_zero, Finset.sum_const_zero]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2),
                Real.log_nonneg (by linarith [show (2 : ℝ) ≤ (M : ℝ) from by exact_mod_cast hM] : (1 : ℝ) ≤ (M : ℝ) - 1)]
    ·
      have hw_pos : 0 < w k := lt_of_le_of_ne (hw_nn k) (Ne.symm hw0)
      have hMw_pos : 0 < (M : ℝ) * w k := mul_pos hM_pos hw_pos

      have hpost_sum : ∑ j, post j = 1 := by
        simp only [hpost_def]
        rw [← Finset.sum_div]
        rw [div_eq_one_iff_eq (ne_of_gt hMw_pos)]

        simp only [hw_def, mixtureMeasure, Measure.smul_apply, smul_eq_mul,
                   Measure.coe_finset_sum, Finset.sum_apply]
        rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
            ENNReal.toReal_natCast]
        rw [ENNReal.toReal_sum (fun i _ => measure_ne_top (P i) _)]
        field_simp
      exact fano_pointwise_entropy_bound M hM post hpost_nn hpost_sum k

  have hweighted := weighted_fano_bound w hw_nn hw_sum h_fn e_fn hbound

  suffices herr : ∑ k, w k * e_fn k =
      (1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal by
    rw [← hLHS, herr] at hweighted
    exact hweighted

  have hwe : ∀ k, w k * e_fn k = w k - (P k (ψ ⁻¹' {k})).toReal / (M : ℝ) := by
    intro k
    simp only [he_def]
    by_cases hw0 : w k = 0
    · have hPk := hPj_zero_of_w_zero k hw0 k
      simp [hw0, hPk]
    · have hw_pos : 0 < w k := lt_of_le_of_ne (hw_nn k) (Ne.symm hw0)
      have hMw_ne : (M : ℝ) * w k ≠ 0 := ne_of_gt (mul_pos hM_pos hw_pos)
      field_simp
  simp_rw [hwe]
  rw [Finset.sum_sub_distrib, hw_sum]


  have hcompl : ∀ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal =
      1 - (P j (ψ ⁻¹' {j})).toReal := by
    intro j
    have hMeasJ : MeasurableSet (ψ ⁻¹' {j}) := hMeas j
    have hc : {ω | ψ ω ≠ j} = (ψ ⁻¹' {j})ᶜ := by ext; simp
    rw [hc, measure_compl hMeasJ (measure_ne_top (P j) _)]
    rw [ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top (P j) _)]
    simp [measure_univ, ENNReal.toReal_one]
  conv_rhs => rw [show ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal =
      ∑ j : Fin M, (1 - (P j (ψ ⁻¹' {j})).toReal) from by
    congr 1; ext j; exact hcompl j]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.smul_one_eq_cast]
  rw [show ∑ k : Fin M, (P k (ψ ⁻¹' {k})).toReal / (M : ℝ) =
      (1 / (M : ℝ)) * ∑ k : Fin M, (P k (ψ ⁻¹' {k})).toReal from by
    rw [Finset.mul_sum]; congr 1; ext k; ring]
  field_simp

/-- Combines `data_processing_kl_partition` with `cond_entropy_fano_bound` to obtain a Fano
inequality in terms of average KL divergence to the mixture and average error probability. -/
theorem fano_conditional_entropy_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    Real.log (M : ℝ) - (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
    Real.log 2 + ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) *
      Real.log ((M : ℝ) - 1) :=
  le_trans (data_processing_kl_partition M hM P hfin_kl ψ hψ) (cond_entropy_fano_bound M hM P ψ hψ)

/-- Reformulation of the Fano conditional entropy bound where the RHS is written as the
average over `j` of the per-index posterior entropy bound. -/
theorem fano_avg_posterior_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    Real.log (M : ℝ) - (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
    (1 / (M : ℝ)) * ∑ j : Fin M,
      (Real.log 2 + (P j {ω | ψ ω ≠ j}).toReal * Real.log ((M : ℝ) - 1)) := by
  have h := fano_conditional_entropy_bound M hM P hfin_kl ψ hψ
  have hM_ne : (M : ℝ) ≠ 0 := by positivity
  have heq : (1 / (M : ℝ)) * ∑ j : Fin M,
      (Real.log 2 + (P j {ω | ψ ω ≠ j}).toReal * Real.log ((M : ℝ) - 1)) =
    Real.log 2 + ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) *
      Real.log ((M : ℝ) - 1) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    field_simp
  linarith

/-- Rearrangement of `fano_conditional_entropy_bound` putting the entropy term and `log 2`
on the right-hand side. -/
lemma fano_entropy_core_bound {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) *
      Real.log ((M : ℝ) - 1) + Real.log 2 ≥
    Real.log (M : ℝ) - (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal :=
  le_of_le_of_eq (fano_conditional_entropy_bound M hM P hfin_kl ψ hψ) (by ring)

/-- Lower bound on the average error probability `(1/M) ∑_j P_j(ψ ≠ j)` obtained from the
Fano conditional entropy bound by solving for the error term (requires `M ≥ 3`). -/
lemma fano_avg_error_bound {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 3 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    (1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥
      1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
          (klDiv (P j) (mixtureMeasure M P)).toReal
        + Real.log 2) / Real.log ((M : ℝ) - 1) := by
  set pe := (1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal
  set I := (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal

  have hM2 : 2 ≤ M := by omega
  have h_core : pe * Real.log ((M : ℝ) - 1) + Real.log 2 ≥
      Real.log (M : ℝ) - I := fano_entropy_core_bound M hM2 P hfin_kl ψ hψ

  have hM_real : (M : ℝ) ≥ 3 := by exact_mod_cast hM
  have hlog_pos : Real.log ((M : ℝ) - 1) > 0 := by
    apply Real.log_pos; linarith
  have hlog_M : Real.log ((M : ℝ) - 1) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log <;> linarith
  rw [ge_iff_le, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hlog_pos]
  nlinarith

/-- Fano's inequality (Theorem 5.10): for any measurable test `ψ : Ω → Fin M` with `M ≥ 3`,
there exists some `j` whose error probability `P_j(ψ ≠ j)` is at least
`1 - ((1/M) ∑_j KL(P_j, P̄) + log 2) / log(M - 1)`. -/
theorem fano_lemma {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 3 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hfin_kl : ∀ j, klDiv (P j) (mixtureMeasure M P) ≠ ⊤)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    ∃ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥
      1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
          (klDiv (P j) (mixtureMeasure M P)).toReal
        + Real.log 2) / Real.log ((M : ℝ) - 1) := by
  set bound := 1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal
    + Real.log 2) / Real.log ((M : ℝ) - 1) with hbound_def
  have h_avg := fano_avg_error_bound M hM P hfin_kl ψ hψ
  by_contra h_none
  push Not at h_none
  have hM_pos : (0 : ℝ) < M := by positivity
  have h_sum_lt : ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal < M * bound := by
    calc ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal
        < ∑ _j : Fin M, bound :=
          Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
            (fun j _ => h_none j)
      _ = M * bound := by simp [Finset.sum_const, nsmul_eq_mul]
  have h_one_div : (1 : ℝ) / M * ∑ j : Fin M,
      (P j {ω | ψ ω ≠ j}).toReal < bound := by
    have : (∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) / M < bound := by
      rwa [div_lt_iff₀ hM_pos, mul_comm]
    rwa [one_div, inv_mul_eq_div]
  linarith

/-- Jensen's inequality for the concave function `log`:
`-log(mean a) ≤ mean(-log a)` for positive reals `a₁, …, a_M`. -/
lemma neg_log_mean_le_mean_neg_log {M : ℕ} (hM : 0 < M)
    (a : Fin M → ℝ) (ha : ∀ k, 0 < a k) :
    -Real.log ((1 / (M : ℝ)) * ∑ k : Fin M, a k) ≤
    (1 / (M : ℝ)) * ∑ k : Fin M, -Real.log (a k) := by
  suffices h : (1 / (M : ℝ)) * ∑ k : Fin M, Real.log (a k) ≤
    Real.log ((1 / (M : ℝ)) * ∑ k : Fin M, a k) by
    have : (1 / (M : ℝ)) * ∑ k : Fin M, -Real.log (a k) =
           -((1 / (M : ℝ)) * ∑ k : Fin M, Real.log (a k)) := by
      simp only [Finset.sum_neg_distrib, mul_neg]
    linarith
  have hconc : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hw_sum : ∑ _i : Fin M, (1 / (M : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have key := hconc.le_map_sum
    (t := Finset.univ)
    (w := fun _ => 1 / (M : ℝ))
    (p := a)
    (fun _ _ => by positivity)
    hw_sum
    (fun i _ => ha i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at key
  exact key

/-- The Radon–Nikodym derivative of a finite sum of probability measures with respect to a
σ-finite reference measure equals the sum of the individual derivatives, almost everywhere. -/
lemma rnDeriv_finset_sum_prob {Ω : Type*} [MeasurableSpace Ω]
    {M : ℕ} (P : Fin M → Measure Ω) (μ : Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] [SigmaFinite μ] :
    (∑ i : Fin M, P i).rnDeriv μ =ᵐ[μ] ∑ i : Fin M, (P i).rnDeriv μ := by
  have : ∀ (s : Finset (Fin M)),
      (∑ i ∈ s, P i).rnDeriv μ =ᵐ[μ] ∑ i ∈ s, (P i).rnDeriv μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact (Measure.rnDeriv_zero μ)
    | @insert a s has IH =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      haveI : SigmaFinite (∑ i ∈ s, P i) := IsFiniteMeasure.toSigmaFinite _
      exact (Measure.rnDeriv_add' _ _ _).trans
        (Filter.EventuallyEq.add (Filter.EventuallyEq.refl _ _) IH)
  simpa using this Finset.univ

/-- The integral of `log(dP_j/dP̄)` under `P_j` is bounded above by the average of
`∫ log(dP_j/dP_k) dP_j` over `k`, by Jensen's inequality applied pointwise to the densities. -/
lemma integral_llr_mixture_le_avg {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (j : Fin M)
    (hfin : ∀ k, klDiv (P j) (P k) ≠ ⊤)
    (h_mix_ne_top : klDiv (P j) (mixtureMeasure M P) ≠ ⊤) :
    ∫ x, MeasureTheory.llr (P j) (mixtureMeasure M P) x ∂(P j) ≤
    (1 / (M : ℝ)) * ∑ k : Fin M, ∫ x, MeasureTheory.llr (P j) (P k) x ∂(P j) := by

  set Psum := ∑ k : Fin M, P k with hPsum_def
  set Pbar := mixtureMeasure M P with hPbar_def
  have hM0 : M ≠ 0 := by omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hME : (M : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hM0
  have h1M_ne_top : (1 / (M : ENNReal)) ≠ ⊤ := by
    rw [one_div]; exact ENNReal.inv_ne_top.mpr hME
  have h1M_ne : (1 / (M : ENNReal)) ≠ 0 := by
    rw [one_div]; exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)

  have hPbar_eq : Pbar = (1 / (M : ENNReal)) • Psum := rfl

  have h_int_bar : Integrable (llr (P j) Pbar) (P j) :=
    (klDiv_ne_top_iff.mp h_mix_ne_top).2
  have h_int_k : ∀ k, Integrable (llr (P j) (P k)) (P j) :=
    fun k => (klDiv_ne_top_iff.mp (hfin k)).2

  have hle : P j ≤ Psum := by
    rw [Measure.le_iff]; intro s _
    rw [Measure.finset_sum_apply]
    exact Finset.single_le_sum (f := fun k => (P k) s)
      (fun k _ => zero_le _) (Finset.mem_univ j)
  have hac_j_sum : P j ≪ Psum := Measure.absolutelyContinuous_of_le hle

  have hac_j_bar : P j ≪ Pbar := by
    intro s hs
    simp only [hPbar_eq, Measure.smul_apply, smul_eq_mul] at hs
    exact hac_j_sum ((mul_eq_zero.mp hs).resolve_left h1M_ne)


  have h_ae_bound : ∀ᵐ x ∂(P j),
      llr (P j) Pbar x ≤ (1 / (M : ℝ)) * ∑ k : Fin M, llr (P j) (P k) x := by

    haveI : IsFiniteMeasure Psum := instIsFiniteMeasureSumMeasure
    haveI : IsFiniteMeasure Pbar := by
      rw [hPbar_eq]; exact Measure.smul_finite _ h1M_ne_top
    haveI : SigmaFinite Pbar := IsFiniteMeasure.toSigmaFinite _


    have h_rnDeriv_smul : Pbar.rnDeriv (P j) =ᵐ[P j]
        (1 / (M : ENNReal)) • Psum.rnDeriv (P j) := by
      rw [hPbar_eq]
      exact Measure.rnDeriv_smul_left_of_ne_top Psum (P j) h1M_ne_top

    have h_rnDeriv_sum : Psum.rnDeriv (P j) =ᵐ[P j]
        ∑ k : Fin M, (P k).rnDeriv (P j) :=
      rnDeriv_finset_sum_prob P (P j)

    have h_all_pos : ∀ᵐ x ∂(P j), ∀ k : Fin M, 0 < (P k).rnDeriv (P j) x := by
      rw [Filter.eventually_all]; intro k
      exact (hac j k).ae_le (Measure.rnDeriv_pos (hac k j))

    have h_all_ne_top : ∀ᵐ x ∂(P j), ∀ k : Fin M, (P k).rnDeriv (P j) x ≠ ⊤ := by
      rw [Filter.eventually_all]; intro k
      exact Measure.rnDeriv_ne_top (P k) (P j)


    have h_neg_llr_bar := neg_llr hac_j_bar
    have h_all_neg_llr_k : ∀ᵐ x ∂(P j), ∀ k : Fin M,
        llr (P j) (P k) x = -llr (P k) (P j) x := by
      rw [Filter.eventually_all]; intro k
      filter_upwards [neg_llr (hac j k)] with x hx
      simp only [Pi.neg_apply] at hx
      linarith

    filter_upwards [h_neg_llr_bar, h_all_neg_llr_k, h_rnDeriv_smul, h_rnDeriv_sum,
                    h_all_pos, h_all_ne_top] with x
      hx_bar hx_k hx_smul hx_sum hx_pos hx_ne_top


    have hx_bar' : llr (P j) Pbar x = -(llr Pbar (P j) x) := by
      simp only [Pi.neg_apply] at hx_bar; linarith


    set a : Fin M → ℝ := fun k => ((P k).rnDeriv (P j) x).toReal with ha_def

    have ha_pos : ∀ k, 0 < a k := by
      intro k
      exact ENNReal.toReal_pos (ne_of_gt (hx_pos k)) (hx_ne_top k)


    have h_bar_val : (Pbar.rnDeriv (P j) x).toReal = (1 / (M : ℝ)) * ∑ k, a k := by
      rw [show Pbar.rnDeriv (P j) x = (1 / (M : ENNReal)) * Psum.rnDeriv (P j) x from by
        rw [hx_smul]; simp [Pi.smul_apply, smul_eq_mul]]
      rw [show Psum.rnDeriv (P j) x = ∑ k : Fin M, (P k).rnDeriv (P j) x from by
        rw [hx_sum]; simp [Finset.sum_apply]]
      rw [ENNReal.toReal_mul]
      congr 1
      · rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
      · rw [ENNReal.toReal_sum (fun k _ => hx_ne_top k)]

    rw [hx_bar']
    show -Real.log ((Pbar.rnDeriv (P j) x).toReal) ≤
      (1 / (M : ℝ)) * ∑ k, llr (P j) (P k) x
    rw [h_bar_val]

    have h_rhs_eq : ∑ k, llr (P j) (P k) x = ∑ k, -Real.log (a k) := by
      apply Finset.sum_congr rfl; intro k _
      rw [hx_k k]
      show -llr (P k) (P j) x = -Real.log (a k)
      simp only [llr, ha_def]
    rw [h_rhs_eq]
    exact neg_log_mean_le_mean_neg_log (by omega : 0 < M) a ha_pos

  have h_int_rhs : Integrable (fun x => (1 / (M : ℝ)) * ∑ k : Fin M,
      llr (P j) (P k) x) (P j) := by
    apply Integrable.const_mul
    exact integrable_finset_sum _ (fun k _ => h_int_k k)
  calc ∫ x, llr (P j) Pbar x ∂(P j)
      ≤ ∫ x, (1 / (M : ℝ)) * ∑ k, llr (P j) (P k) x ∂(P j) :=
        integral_mono_ae h_int_bar h_int_rhs h_ae_bound
    _ = (1 / (M : ℝ)) * ∫ x, ∑ k, llr (P j) (P k) x ∂(P j) := by
        rw [integral_const_mul]
    _ = (1 / (M : ℝ)) * ∑ k, ∫ x, llr (P j) (P k) x ∂(P j) := by
        congr 1; exact integral_finset_sum _ (fun k _ => h_int_k k)

/-- Convexity of KL divergence in its second argument applied to the uniform mixture:
`KL(P_j, P̄) ≤ (1/M) ∑_k KL(P_j, P_k)`. -/
theorem kl_convex_in_second_arg {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (j : Fin M)
    (hfin : ∀ k, klDiv (P j) (P k) ≠ ⊤) :
    (klDiv (P j) (mixtureMeasure M P)).toReal ≤
    (1 / (M : ℝ)) * ∑ k : Fin M, (klDiv (P j) (P k)).toReal := by
  have hM_pos : 0 < M := by omega

  haveI h_mix_prob : IsProbabilityMeasure (mixtureMeasure M P) := by
    constructor
    simp only [mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finset_sum,
               Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
               Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [one_div, ENNReal.inv_mul_cancel]
    · exact_mod_cast hM_pos.ne'
    · exact ENNReal.natCast_ne_top M

  have h_rhs_nn : 0 ≤ (1 / (M : ℝ)) * ∑ k : Fin M, (klDiv (P j) (P k)).toReal :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

  by_cases h_top : klDiv (P j) (mixtureMeasure M P) = ⊤
  · rw [h_top, ENNReal.toReal_top]; exact h_rhs_nn

  have h_prob_eq : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν],
      (P j) Set.univ = ν Set.univ := by
    intros; simp [measure_univ]
  rw [toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp h_top).1 (h_prob_eq (mixtureMeasure M P))]
  have h_rhs_eq : (1 / (M : ℝ)) * ∑ k, (klDiv (P j) (P k)).toReal =
      (1 / (M : ℝ)) * ∑ k, ∫ x, MeasureTheory.llr (P j) (P k) x ∂(P j) := by
    congr 1; apply Finset.sum_congr rfl; intro k _
    exact toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp (hfin k)).1 (h_prob_eq (P k))
  rw [h_rhs_eq]
  exact integral_llr_mixture_le_avg M hM P hac j hfin h_top

/-- Averaging `kl_convex_in_second_arg` over `j` gives the mixture-to-pairwise bound
`avg_j KL(P_j, P̄) ≤ (1/M²) ∑_{j,k} KL(P_j, P_k)` used in Fano's inequality. -/
theorem kl_mixture_le_avg_pairwise {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (hac : ∀ j k, P j ≪ P k)
    (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
    (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal := by
  have h_pw : ∀ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
      (1 / (M : ℝ)) * ∑ k : Fin M, (klDiv (P j) (P k)).toReal :=
    fun j => kl_convex_in_second_arg M hM P hac j (hfin j)
  have h_sum : ∑ j : Fin M, (klDiv (P j) (mixtureMeasure M P)).toReal ≤
      ∑ j : Fin M, ((1 / (M : ℝ)) * ∑ k : Fin M, (klDiv (P j) (P k)).toReal) :=
    Finset.sum_le_sum (fun j _ => h_pw j)
  rw [← Finset.mul_sum] at h_sum
  have h_div : (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P j) (mixtureMeasure M P)).toReal ≤
      (1 / (M : ℝ)) * ((1 / (M : ℝ)) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal) :=
    mul_le_mul_of_nonneg_left h_sum (by positivity)
  calc (1 / (M : ℝ)) * ∑ j : Fin M,
        (klDiv (P j) (mixtureMeasure M P)).toReal
      ≤ (1 / (M : ℝ)) * ((1 / (M : ℝ)) * ∑ j : Fin M, ∑ k : Fin M,
        (klDiv (P j) (P k)).toReal) := h_div
    _ = (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
        (klDiv (P j) (P k)).toReal := by ring

/-- Trivial upper bound on each KL divergence to the mixture: `KL(P_j, P̄) ≤ log M`,
since `dP_j/dP̄ ≤ M` almost everywhere. -/
lemma klDiv_component_le_log_M
    {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω)
    [∀ j, IsProbabilityMeasure (P j)]
    (j : Fin M) :
    (klDiv (P j) (mixtureMeasure M P)).toReal ≤ Real.log (M : ℝ) := by
  set Pbar := mixtureMeasure M P
  set Psum := ∑ k : Fin M, P k
  have hM0 : M ≠ 0 := by omega
  have hME : (M : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hM0
  have h1M_ne : (1 / (M : ENNReal)) ≠ 0 := by
    rw [one_div]; exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
  have h1M_ne_top : (1 / (M : ENNReal)) ≠ ⊤ := by
    rw [one_div]; exact ENNReal.inv_ne_top.mpr hME
  haveI : IsFiniteMeasure Pbar :=
    Psum.smul_finite (show (1 / (M : ENNReal)) ≠ ⊤ from h1M_ne_top)
  have hle : P j ≤ Psum := by
    rw [Measure.le_iff]; intro s _
    rw [Measure.finset_sum_apply]
    exact Finset.single_le_sum (f := fun k => (P k) s) (fun k _ => zero_le _) (Finset.mem_univ j)
  have hac_j_sum : P j ≪ Psum := Measure.absolutelyContinuous_of_le hle
  have hac : P j ≪ Pbar := by
    intro s hs
    simp only [Pbar, mixtureMeasure, Measure.smul_apply, smul_eq_mul] at hs
    exact hac_j_sum ((mul_eq_zero.mp hs).resolve_left h1M_ne)
  have h_eq : P j Set.univ = Pbar Set.univ := by
    rw [IsProbabilityMeasure.measure_univ]
    simp only [Pbar, mixtureMeasure, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
    simp only [IsProbabilityMeasure.measure_univ, Finset.sum_const, Finset.card_fin,
               nsmul_eq_mul, mul_one]
    rw [one_div, ENNReal.inv_mul_cancel hME (ENNReal.natCast_ne_top M)]
  rw [toReal_klDiv_of_measure_eq hac h_eq]
  have hM_real_ge : (2 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases h_int : Integrable (llr (P j) Pbar) (P j)
  · have h_rnDeriv_smul := Measure.rnDeriv_smul_right_of_ne_top (P j) Psum h1M_ne h1M_ne_top
    have h_rnDeriv_le := Measure.rnDeriv_le_one_of_le hle
    have h_rnDeriv_bound_j : ∀ᵐ x ∂(P j), (P j).rnDeriv Pbar x ≤ (M : ENNReal) := by
      apply hac_j_sum.ae_le
      filter_upwards [h_rnDeriv_smul, h_rnDeriv_le] with x hx1 hx2
      show (P j).rnDeriv Pbar x ≤ (M : ENNReal)
      rw [show Pbar = (1 / (M : ENNReal)) • Psum from rfl, hx1]
      simp only [one_div, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hx2 ⊢
      rw [inv_inv]
      exact mul_le_of_le_one_right (zero_le _) hx2
    have h_llr_bound : ∀ᵐ x ∂(P j), llr (P j) Pbar x ≤ Real.log (M : ℝ) := by
      filter_upwards [h_rnDeriv_bound_j] with x hx
      show Real.log ((P j).rnDeriv Pbar x).toReal ≤ Real.log (M : ℝ)
      have hx_ne_top := ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) hx
      have hx_real : ((P j).rnDeriv Pbar x).toReal ≤ (M : ℝ) := by
        rw [← ENNReal.toReal_natCast M]
        exact (ENNReal.toReal_le_toReal hx_ne_top (ENNReal.natCast_ne_top M)).mpr hx
      by_cases h0 : (P j).rnDeriv Pbar x = 0
      · simp [h0]; exact Real.log_nonneg (by linarith)
      · exact Real.log_le_log (ENNReal.toReal_pos h0 hx_ne_top) hx_real
    calc ∫ x, llr (P j) Pbar x ∂(P j)
        ≤ ∫ _x, Real.log (M : ℝ) ∂(P j) :=
          integral_mono_ae h_int (integrable_const _) h_llr_bound
      _ = Real.log (M : ℝ) := by
          simp [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
                ENNReal.toReal_one]
  · rw [integral_undef h_int]
    exact Real.log_nonneg (by linarith)

/-- Squared Euclidean distance between two vectors `θ₁, θ₂ ∈ ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- Squared Euclidean distance is symmetric: `sqDist a b = sqDist b a`. -/
lemma sqDist_symm {d : ℕ} (a b : Fin d → ℝ) : sqDist a b = sqDist b a := by
  simp only [sqDist]; congr 1; ext i; ring

/-- Quasi-triangle inequality for squared Euclidean distance:
`sqDist a c ≤ 2 (sqDist a b + sqDist b c)`. -/
lemma sqDist_quasi_triangle {d : ℕ} (a b c : Fin d → ℝ) :
    sqDist a c ≤ 2 * (sqDist a b + sqDist b c) := by
  simp only [sqDist]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  nlinarith [sq_nonneg (a i - b i), sq_nonneg (b i - c i),
             sq_nonneg (a i - b i - (b i - c i))]

/-- `isMinIdx f n` holds when `n < M` and `f ⟨n, _⟩` is a minimum of `f` over `Fin M`. -/
def isMinIdx {M : ℕ} (f : Fin M → ℝ) (n : ℕ) : Prop :=
  ∃ h : n < M, ∀ k : Fin M, f ⟨n, h⟩ ≤ f k

/-- Decidability instance for `isMinIdx`, obtained classically. -/
instance isMinIdx.decidable {M : ℕ} (f : Fin M → ℝ) : DecidablePred (isMinIdx f) :=
  fun _ => Classical.dec _

/-- A nonempty finite real-valued function has at least one minimising index. -/
lemma exists_isMinIdx {M : ℕ} (f : Fin M → ℝ) (hM : 0 < M) : ∃ n, isMinIdx f n := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin M)) f
    ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  exact ⟨j.val, j.isLt, fun k => hj k (Finset.mem_univ _)⟩

/-- Deterministic nearest-neighbour argmin operator: returns the smallest minimising index
of `f : Fin M → ℝ` (with `M > 0`). -/
def nnArgmin {M : ℕ} (f : Fin M → ℝ) (hM : 0 < M) : Fin M :=
  ⟨Nat.find (exists_isMinIdx f hM), (Nat.find_spec (exists_isMinIdx f hM)).choose⟩

/-- Defining property of `nnArgmin`: the value at the chosen index is minimal. -/
lemma nnArgmin_spec {M : ℕ} (f : Fin M → ℝ) (hM : 0 < M) (k : Fin M) :
    f (nnArgmin f hM) ≤ f k :=
  (Nat.find_spec (exists_isMinIdx f hM)).choose_spec k

/-- Measurability of `Y ↦ sqDist (θ̂(Y)) c` whenever `θ̂` is measurable. -/
lemma measurable_sqDist_apply {d : ℕ} {θhat : (Fin d → ℝ) → Fin d → ℝ}
    (hθhat : Measurable θhat) (c : Fin d → ℝ) :
    Measurable (fun Y => sqDist (θhat Y) c) := by
  unfold sqDist
  apply Finset.measurable_sum; intro i _
  exact ((measurable_pi_apply i).comp hθhat |>.sub measurable_const).pow measurable_const

/-- The nearest-neighbour classifier `Y ↦ argmin_j ‖θ̂(Y) - θ_j‖²` is measurable. -/
theorem nn_classifier_measurable {d M : ℕ}
    (θ : Fin M → Fin d → ℝ) (θhat : (Fin d → ℝ) → Fin d → ℝ)
    (hθhat : Measurable θhat) (hM : 0 < M) :
    Measurable (fun Y => nnArgmin (fun j => sqDist (θhat Y) (θ j)) hM) := by
  unfold nnArgmin
  apply measurable_to_countable'
  intro j
  have : (fun Y => (⟨Nat.find (exists_isMinIdx (fun j => sqDist (θhat Y) (θ j)) hM),
       (Nat.find_spec (exists_isMinIdx (fun j => sqDist (θhat Y) (θ j)) hM)).choose⟩ : Fin M)) ⁻¹' {j}
      = (fun Y => Nat.find (exists_isMinIdx (fun j => sqDist (θhat Y) (θ j)) hM)) ⁻¹' {j.val} := by
    ext Y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
  rw [this]
  have hmeas : Measurable (fun Y =>
      Nat.find (exists_isMinIdx (fun j => sqDist (θhat Y) (θ j)) hM)) := by
    apply measurable_find; intro k; unfold isMinIdx
    by_cases hk : k < M
    · have : {x | ∃ h : k < M, ∀ (k_1 : Fin M),
            sqDist (θhat x) (θ ⟨k, h⟩) ≤ sqDist (θhat x) (θ k_1)}
          = ⋂ j : Fin M, {x | sqDist (θhat x) (θ ⟨k, hk⟩) ≤ sqDist (θhat x) (θ j)} := by
        ext x; constructor
        · rintro ⟨_, h⟩; exact Set.mem_iInter.mpr h
        · intro h; exact ⟨hk, Set.mem_iInter.mp h⟩
      rw [this]
      exact .iInter fun j =>
        measurableSet_le (measurable_sqDist_apply hθhat _) (measurable_sqDist_apply hθhat _)
    · convert MeasurableSet.empty; ext x; simp [hk]
  exact hmeas (measurableSet_singleton _)

/-- Reduction from estimation to testing via Fano's inequality: if `θ_1, …, θ_M` are
`4ϕ`-separated in squared distance and the average pairwise KL divergence is at most `κ`,
then any estimator suffers worst-case probability of error at least
`1 - (κ + log 2)/log(M - 1)` at radius `ϕ`. -/
theorem reduction_to_testing_fano
    {d : ℕ} {M : ℕ} (hM : 3 ≤ M)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (θ : Fin M → Fin d → ℝ)
    [∀ j, IsProbabilityMeasure (P (θ j))]
    (hac : ∀ j k, P (θ j) ≪ P (θ k))
    (hfin : ∀ j k, klDiv (P (θ j)) (P (θ k)) ≠ ⊤)
    (ϕ : ℝ) (hϕ : 0 < ϕ)
    (hsep : ∀ j k : Fin M, j ≠ k → sqDist (θ j) (θ k) ≥ 4 * ϕ)
    (κ : ℝ) (hκ : (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P (θ j)) (P (θ k))).toReal ≤ κ)
    (θhat : (Fin d → ℝ) → (Fin d → ℝ))
    (hθhat : Measurable θhat) :
      ⨆ (j : Fin M), (P (θ j) {Y | sqDist (θhat Y) (θ j) ≥ ϕ}).toReal ≥
    1 - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) := by
  rw [ge_iff_le]
  have hM_pos : 0 < M := by omega
  classical

  let P' : Fin M → Measure (Fin d → ℝ) := fun j => P (θ j)


  let ψ : (Fin d → ℝ) → Fin M := fun Y =>
    nnArgmin (fun j => sqDist (θhat Y) (θ j)) hM_pos

  have hψ_spec : ∀ Y j, sqDist (θhat Y) (θ (ψ Y)) ≤ sqDist (θhat Y) (θ j) := by
    intro Y j
    exact nnArgmin_spec (fun j => sqDist (θhat Y) (θ j)) hM_pos j


  have hψ_meas : Measurable ψ := nn_classifier_measurable θ θhat hθhat hM_pos


  have hfin_kl : ∀ j, klDiv (P' j) (mixtureMeasure M P') ≠ ⊤ :=
    fun j => klDiv_mixture_ne_top M (by omega) P' hac hfin j

  obtain ⟨j₀, hj₀⟩ := fano_lemma M hM P' hfin_kl ψ hψ_meas

  have hM2 : 2 ≤ M := by omega
  have hkl := kl_mixture_le_avg_pairwise M hM2 P' hac hfin
  have hA_le_κ : (1 / (M : ℝ)) * ∑ j : Fin M,
      (klDiv (P' j) (mixtureMeasure M P')).toReal ≤ κ := le_trans hkl hκ

  have hlog_nonneg : 0 ≤ Real.log ((M : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (M : ℝ) ≥ 2 := by exact_mod_cast hM2
    linarith
  have hbound : 1 - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≤
      1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
          (klDiv (P' j) (mixtureMeasure M P')).toReal
        + Real.log 2) / Real.log ((M : ℝ) - 1) := by
    have h1 : (1 / (M : ℝ)) * ∑ j : Fin M,
        (klDiv (P' j) (mixtureMeasure M P')).toReal + Real.log 2 ≤ κ + Real.log 2 := by
      linarith
    have h2 : ((1 / (M : ℝ)) * ∑ j : Fin M,
        (klDiv (P' j) (mixtureMeasure M P')).toReal + Real.log 2) /
        Real.log ((M : ℝ) - 1) ≤ (κ + Real.log 2) / Real.log ((M : ℝ) - 1) :=
      div_le_div_of_nonneg_right h1 hlog_nonneg
    linarith


  have h_incl : {Y | ψ Y ≠ j₀} ⊆ {Y | sqDist (θhat Y) (θ j₀) ≥ ϕ} := by
    intro Y hY
    simp only [Set.mem_setOf_eq] at hY ⊢
    have hsep_jk := hsep j₀ (ψ Y) (Ne.symm hY)
    have htri := sqDist_quasi_triangle (θ j₀) (θhat Y) (θ (ψ Y))
    rw [sqDist_symm (θ j₀) (θhat Y)] at htri
    linarith [hψ_spec Y j₀]

  have h_chain : 1 - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≤
      (P (θ j₀) {Y | sqDist (θhat Y) (θ j₀) ≥ ϕ}).toReal := by
    calc 1 - (κ + Real.log 2) / Real.log ((M : ℝ) - 1)
        ≤ 1 - ((1 / (M : ℝ)) * ∑ j : Fin M,
            (klDiv (P' j) (mixtureMeasure M P')).toReal
          + Real.log 2) / Real.log ((M : ℝ) - 1) := hbound
      _ ≤ (P' j₀ {ω | ψ ω ≠ j₀}).toReal := hj₀
      _ = (P (θ j₀) {Y | ψ Y ≠ j₀}).toReal := rfl
      _ ≤ (P (θ j₀) {Y | sqDist (θhat Y) (θ j₀) ≥ ϕ}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_incl)

  have h_bdd : BddAbove (Set.range
      (fun j => (P (θ j) {Y | sqDist (θhat Y) (θ j) ≥ ϕ}).toReal)) := by
    use 1
    rintro _ ⟨j, rfl⟩
    have h1 : P (θ j) {Y | sqDist (θhat Y) (θ j) ≥ ϕ} ≤ 1 := prob_le_one
    rw [show (1 : ℝ) = (1 : ENNReal).toReal from by simp]
    exact ENNReal.toReal_mono (by simp) h1
  exact le_ciSup_of_le h_bdd j₀ h_chain

/-- The Gaussian-like density assumption: `P θ₁` equals `P θ₂` re-weighted by the
exponential-quadratic likelihood ratio expected from the Gaussian location family. -/
theorem gaussian_family_withDensity
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (θ₁ θ₂ : Fin d → ℝ) :
    P θ₁ = (P θ₂).withDensity (fun Y => ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
      ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))) :=
  hDensity θ₁ θ₂

/-- Absolute continuity `P θ₁ ≪ P θ₂` for any two parameters in a Gaussian-like location
family, derived from the explicit density assumption. -/
theorem gaussian_family_ac
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (θ₁ θ₂ : Fin d → ℝ) :
    (P θ₁).AbsolutelyContinuous (P θ₂) := by
  rw [gaussian_family_withDensity σ hσ n hn P hGSM hDensity θ₁ θ₂]
  exact withDensity_absolutelyContinuous (P θ₂) _

/-- Coordinate-mean hypothesis: under `P θ` the expectation of the `i`-th coordinate is `θ i`. -/
theorem gaussian_family_coord_mean
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hCoordMean : ∀ (θ : Fin d → ℝ) (i : Fin d), ∫ Y, Y i ∂(P θ) = θ i)
    (θ : Fin d → ℝ) (i : Fin d) :
    ∫ Y, Y i ∂(P θ) = θ i := hCoordMean θ i

/-- Centered coordinate mean: `∫ (Y_i - θ_i) d P θ = 0`, derived from the coordinate-mean
hypothesis. -/
theorem gaussian_family_mean
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hCoordMean : ∀ (θ : Fin d → ℝ) (i : Fin d), ∫ Y, Y i ∂(P θ) = θ i)
    (θ : Fin d → ℝ) (i : Fin d) :
    ∫ Y, (Y i - θ i) ∂(P θ) = 0 := by

  have hInt : Integrable (fun Y => Y i - θ i) (P θ) := by
    have hIntSq : Integrable (fun Y => (Y i - θ i) ^ 2) (P θ) := by
      by_contra h
      have h1 := integral_undef h
      rw [hGSM θ i] at h1
      have : σ ^ 2 / ↑n > 0 := div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)
      linarith
    have hAE : AEStronglyMeasurable (fun Y : Fin d → ℝ => Y i - θ i) (P θ) :=
      ((continuous_apply i).sub continuous_const).aestronglyMeasurable
    exact ((memLp_two_iff_integrable_sq hAE).mpr hIntSq).integrable one_le_two

  have hIntYi : Integrable (fun Y : Fin d → ℝ => Y i) (P θ) := by
    have : (fun Y : Fin d → ℝ => Y i) = (fun Y => (Y i - θ i) + θ i) := by ext; ring
    rw [this]
    exact hInt.add (integrable_const _)

  have hMean := gaussian_family_coord_mean σ hσ n hn P hGSM hCoordMean θ i
  rw [integral_sub hIntYi (integrable_const _), hMean, integral_const]
  simp

/-- Explicit formula for the Radon–Nikodym derivative `d P θ₁ / d P θ₂` in a Gaussian-like
location family, valid `P θ₁`-almost everywhere. -/
theorem gaussian_family_rnDeriv_ae
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (θ₁ θ₂ : Fin d → ℝ) :
    (P θ₁).rnDeriv (P θ₂) =ᵐ[P θ₁]
      fun Y => ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2))) := by

  have hwd := gaussian_family_withDensity σ hσ n hn P hGSM hDensity θ₁ θ₂

  have hf_meas : Measurable (fun Y : Fin d → ℝ => ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
      ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).sub measurable_const).pow_const 2 |>.sub
      (((measurable_pi_apply i).sub measurable_const).pow_const 2)

  have h_ae_ν : (P θ₁).rnDeriv (P θ₂) =ᵐ[P θ₂]
      fun Y => ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2))) := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity (P θ₂) hf_meas

  exact (gaussian_family_ac σ hσ n hn P hGSM hDensity θ₁ θ₂).ae_eq h_ae_ν

/-- Explicit formula for the log-likelihood ratio `log(d P θ₁ / d P θ₂)` in a Gaussian-like
location family, valid `P θ₁`-almost everywhere. -/
theorem gaussian_family_llr_ae
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (θ₁ θ₂ : Fin d → ℝ) :
    llr (P θ₁) (P θ₂) =ᵐ[P θ₁]
      fun Y => (↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2) := by
  have hrnDeriv := gaussian_family_rnDeriv_ae σ hσ n hn P hGSM hDensity θ₁ θ₂
  filter_upwards [hrnDeriv] with Y hY
  simp only [llr, hY]
  rw [ENNReal.toReal_ofReal (le_of_lt (exp_pos _))]
  exact Real.log_exp _

/-- Each centered coordinate `Y i - θ i` is integrable under `P θ`, using square-integrability
from the variance hypothesis. -/
theorem gaussian_family_coord_integrable
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (θ : Fin d → ℝ) (i : Fin d) :
    Integrable (fun Y => Y i - θ i) (P θ) := by
  have hIntSq : Integrable (fun Y => (Y i - θ i) ^ 2) (P θ) := by
    by_contra h
    have h1 := integral_undef h
    rw [hGSM θ i] at h1
    have : σ ^ 2 / ↑n > 0 := div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)
    linarith
  have hAE : AEStronglyMeasurable (fun Y : Fin d → ℝ => Y i - θ i) (P θ) :=
    ((continuous_apply i).sub continuous_const).aestronglyMeasurable
  exact ((memLp_two_iff_integrable_sq hAE).mpr hIntSq).integrable one_le_two

/-- The quadratic difference `(Y_i - θ₂_i)² - (Y_i - θ₁_i)²` is integrable under `P θ₁`. -/
theorem gaussian_family_quad_integrable
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (θ₁ θ₂ : Fin d → ℝ) (i : Fin d) :
    Integrable (fun Y => (Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2) (P θ₁) := by
  have hIntSq1 : Integrable (fun Y => (Y i - θ₁ i) ^ 2) (P θ₁) := by
    by_contra h
    have h1 := integral_undef h
    rw [hGSM θ₁ i] at h1
    have : σ ^ 2 / ↑n > 0 := div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr hn)
    linarith
  have hIntCoord1 : Integrable (fun Y => Y i - θ₁ i) (P θ₁) :=
    gaussian_family_coord_integrable σ hσ n hn P hGSM θ₁ i
  have hIntSq2 : Integrable (fun Y => (Y i - θ₂ i) ^ 2) (P θ₁) := by
    have : (fun Y : Fin d → ℝ => (Y i - θ₂ i) ^ 2) =
        (fun Y => (Y i - θ₁ i) ^ 2 + 2 * (θ₁ i - θ₂ i) * (Y i - θ₁ i) + (θ₁ i - θ₂ i) ^ 2) := by
      ext Y; ring
    rw [this]
    exact (hIntSq1.add (hIntCoord1.const_mul _)).add (integrable_const _)
  exact hIntSq2.sub hIntSq1

/-- The log-likelihood ratio `llr (P θ₁) (P θ₂)` is integrable under `P θ₁` in the
Gaussian-like location family. -/
theorem gaussian_family_llr_integrable
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (θ₁ θ₂ : Fin d → ℝ) :
    Integrable (llr (P θ₁) (P θ₂)) (P θ₁) := by

  have hQuadInt : Integrable (fun Y => (↑n / (2 * σ ^ 2)) *
      ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)) (P θ₁) :=
    (integrable_finset_sum _ (fun i _ =>
      gaussian_family_quad_integrable σ hσ n hn P hGSM θ₁ θ₂ i)).const_mul _

  exact hQuadInt.congr (gaussian_family_llr_ae σ hσ n hn P hGSM hDensity θ₁ θ₂).symm

set_option maxHeartbeats 400000 in
/-- Closed-form integral of the log-likelihood ratio for a Gaussian-like family:
`∫ llr(P θ₁, P θ₂) d P θ₁ = n · ‖θ₁ - θ₂‖² / (2 σ²)`, alongside absolute continuity and
integrability of the integrand. -/
theorem gaussian_family_llr_integral
    {d : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]
    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (hCoordMean : ∀ (θ : Fin d → ℝ) (i : Fin d), ∫ Y, Y i ∂(P θ) = θ i) :

    ∀ (θ₁ θ₂ : Fin d → ℝ),
      (P θ₁).AbsolutelyContinuous (P θ₂) ∧
      Integrable (llr (P θ₁) (P θ₂)) (P θ₁) ∧
      ∫ Y, llr (P θ₁) (P θ₂) Y ∂(P θ₁) = ↑n * sqDist θ₁ θ₂ / (2 * σ ^ 2) := by
  intro θ₁ θ₂
  refine ⟨gaussian_family_ac σ hσ n hn P hGSM hDensity θ₁ θ₂,
          gaussian_family_llr_integrable σ hσ n hn P hGSM hDensity θ₁ θ₂, ?_⟩

  rw [integral_congr_ae (gaussian_family_llr_ae σ hσ n hn P hGSM hDensity θ₁ θ₂)]

  rw [integral_const_mul]

  rw [integral_finset_sum _
    (fun i _ => gaussian_family_quad_integrable σ hσ n hn P hGSM θ₁ θ₂ i)]


  have hcoord : ∀ i : Fin d,
      ∫ Y, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2) ∂(P θ₁) = (θ₁ i - θ₂ i) ^ 2 := by
    intro i

    have hconv : (fun Y : Fin d → ℝ =>
        (Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2) =
        (fun Y => 2 * (θ₁ i - θ₂ i) * (Y i - θ₁ i) + (θ₁ i - θ₂ i) ^ 2) := by
      ext Y; ring
    rw [hconv]
    have hIntC := gaussian_family_coord_integrable σ hσ n hn P hGSM θ₁ i
    rw [integral_add (hIntC.const_mul _) (integrable_const _)]
    rw [integral_const_mul, gaussian_family_mean σ hσ n hn P hGSM hCoordMean θ₁ i, integral_const]
    simp
  simp_rw [hcoord]

  unfold sqDist
  ring

/-- Closed-form KL divergence for a Gaussian-like family:
`KL(P θ₁, P θ₂) = n · ‖θ₁ - θ₂‖² / (2 σ²)`. -/
theorem gaussian_kl_divergence
    {d : ℕ} (θ₁ θ₂ : Fin d → ℝ)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    [∀ θ, IsProbabilityMeasure (P θ)]

    (hGSM : ∀ (θ : Fin d → ℝ) (i : Fin d),
      ∫ Y, (Y i - θ i) ^ 2 ∂(P θ) = σ ^ 2 / ↑n)
    (hDensity : ∀ θ₁ θ₂ : Fin d → ℝ, P θ₁ = (P θ₂).withDensity (fun Y =>
      ENNReal.ofReal (exp ((↑n / (2 * σ ^ 2)) *
        ∑ i : Fin d, ((Y i - θ₂ i) ^ 2 - (Y i - θ₁ i) ^ 2)))))
    (hCoordMean : ∀ (θ : Fin d → ℝ) (i : Fin d), ∫ Y, Y i ∂(P θ) = θ i) :
    (klDiv (P θ₁) (P θ₂)).toReal = ↑n * sqDist θ₁ θ₂ / (2 * σ ^ 2) := by

  obtain ⟨hac, hint, hllr⟩ := gaussian_family_llr_integral σ hσ n hn P hGSM hDensity hCoordMean θ₁ θ₂

  rw [klDiv_of_ac_of_integrable hac hint]

  simp only [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [hllr]

  ring_nf
  rw [ENNReal.toReal_ofReal]

  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · exact Nat.cast_nonneg' n
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact sq_nonneg σ⁻¹
  · linarith

/-- Hamming distance between two Boolean vectors: the number of coordinates where they differ. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- Hamming distance is symmetric. -/
lemma hammingDist_symm {d : ℕ} (ω₁ ω₂ : Fin d → Bool) :
    hammingDist ω₁ ω₂ = hammingDist ω₂ ω₁ := by
  simp only [hammingDist]; congr 1; ext i; simp [ne_comm]

/-- Equivalence between the subtype `{i ∈ {j, k}}` and `Fin 2`, sending `j` to `0` and `k`
to `1`, for distinct indices `j ≠ k`. -/
noncomputable def pairSubtypeEquivFin2 {M : ℕ} (j k : Fin M) (hjk : j ≠ k) :
    {i : Fin M // i ∈ ({j, k} : Finset (Fin M))} ≃ Fin 2 where
  toFun := fun ⟨i, hi⟩ => if i = j then 0 else 1
  invFun := fun n => if h : n = 0 then ⟨j, Finset.mem_insert.mpr (Or.inl rfl)⟩
    else ⟨k, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  left_inv := by
    intro ⟨i, hi⟩; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    cases hi with
    | inl h => subst h; simp
    | inr h => subst h; simp [hjk.symm, show (1 : Fin 2) ≠ 0 from by decide]
  right_inv := by
    intro n; fin_cases n
    · simp
    · simp only [show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, dite_false]; simp [hjk.symm]

/-- For distinct indices `j ≠ k`, the space of functions `Fin M → α` is equivalent to the
product of `α × α` (the values at `j` and `k`) and the functions on the complementary indices. -/
noncomputable def fiberEquiv {M : ℕ} (j k : Fin M) (hjk : j ≠ k) (α : Type*) :
    (Fin M → α) ≃ (α × α) × ({i : Fin M // i ∉ ({j, k} : Finset (Fin M))} → α) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ ({j, k} : Finset (Fin M))) (fun _ => α)).trans
    (Equiv.prodCongrLeft fun _ =>
      ((Equiv.piCongrLeft' (fun _ => α) (pairSubtypeEquivFin2 j k hjk)).trans
        (finTwoArrowEquiv α)))

/-- The first component of `fiberEquiv j k hjk α ω` is the pair `(ω j, ω k)`. -/
lemma fiberEquiv_fst {M : ℕ} (j k : Fin M) (hjk : j ≠ k) (α : Type*) (ω : Fin M → α) :
    (fiberEquiv j k hjk α ω).1 = (ω j, ω k) := by
  ext <;> simp [fiberEquiv, Equiv.piEquivPiSubtypeProd, Equiv.piCongrLeft',
    pairSubtypeEquivFin2, finTwoArrowEquiv, show (1 : Fin 2) ≠ 0 from by decide]

open ProbabilityTheory in
/-- The uniform probability measure on `Bool`. -/
noncomputable def μ_Bool : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- The uniform Boolean measure `μ_Bool` is a probability measure. -/
instance μ_Bool_prob : IsProbabilityMeasure μ_Bool :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Centering map sending `true ↦ 1/2` and `false ↦ -1/2`, used to turn Boolean variables
into centered `±1/2`-valued random variables. -/
noncomputable def boolCenter (b : Bool) : ℝ := if b then (1 : ℝ) / 2 else -(1 : ℝ) / 2

/-- Each singleton has measure `1/2` under the uniform measure on `Bool`. -/
lemma μ_Bool_singleton (b : Bool) : μ_Bool {b} = 1 / 2 := by
  show (PMF.uniformOfFintype Bool).toMeasure {b} = 1 / 2
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply, Fintype.card_bool]

/-- The centered Bernoulli random variable `boolCenter` has zero mean under `μ_Bool`. -/
lemma integral_boolCenter_zero : ∫ b, boolCenter b ∂μ_Bool = 0 := by
  rw [integral_fintype (hf := Integrable.of_finite)]
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv, Finset.sum_pair (by decide : true ≠ false)]
  simp only [boolCenter, Bool.false_eq_true, ↓reduceIte, Measure.real_def]
  rw [show (μ_Bool {true}).toReal = 1 / 2 from by rw [μ_Bool_singleton]; simp,
      show (μ_Bool {false}).toReal = 1 / 2 from by rw [μ_Bool_singleton]; simp]
  simp [smul_eq_mul]; ring

/-- Each coordinate `ω ↦ boolCenter (ω i)` has zero mean under the uniform product measure on
`Fin d → Bool`. -/
lemma mean_boolCenter_coord_zero (d : ℕ) (i : Fin d) :
    ∫ ω, boolCenter (ω i) ∂(Measure.pi (fun (_ : Fin d) => μ_Bool)) = 0 := by
  rw [integral_comp_eval (hf := AEStronglyMeasurable.of_discrete)]
  exact integral_boolCenter_zero

/-- Under the uniform product measure on `Fin d → Bool`, the coordinate maps
`ω ↦ boolCenter (ω i)` are mutually independent. -/
lemma indep_boolCenter_coords (d : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Fin d → Bool) => boolCenter (ω i))
      (Measure.pi (fun (_ : Fin d) => μ_Bool)) :=
  ProbabilityTheory.iIndepFun_pi (X := fun (_ : Fin d) => boolCenter)
    (fun _ => AEMeasurable.of_discrete)

/-- Private cancellation lemma for the Boolean XOR: `a ^^ (a ^^ b) = b`. -/
@[simp] private lemma Bool.xor_xor_cancel_left' (a b : Bool) : a ^^ (a ^^ b) = b := by
  cases a <;> cases b <;> rfl

/-- The "XOR pairing" self-equivalence on `(Fin d → Bool) × (Fin d → Bool)`, sending
`(a, b)` to `(a, a ^^ b)`. Used to reduce pair-counting arguments to single-string counts. -/
def pairXorEquiv (d : ℕ) :
    (Fin d → Bool) × (Fin d → Bool) ≃ (Fin d → Bool) × (Fin d → Bool) where
  toFun p := (p.1, fun i => p.1 i ^^ p.2 i)
  invFun q := (q.1, fun i => q.1 i ^^ q.2 i)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The sum of `boolCenter (c i)` over `i` equals the Hamming weight (number of `true`s)
of `c` minus `d/2`. -/
lemma boolCenter_sum_eq_weight {d : ℕ} (c : Fin d → Bool) :
    ∑ i : Fin d, boolCenter (c i) =
    (∑ i : Fin d, if (c i) = true then (1:ℝ) else 0) - (d:ℝ) / 2 := by
  have : ∀ i : Fin d, boolCenter (c i) = (if c i = true then (1:ℝ) else 0) - 1/2 := by
    intro i; unfold boolCenter; cases (c i) <;> simp <;> ring
  simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

/-- The Hamming distance between `a` and `b` equals the sum over coordinates of the indicator
`a i ^^ b i = true`, cast to `ℝ`. -/
lemma hammingDist_cast_eq' {d : ℕ} (a b : Fin d → Bool) :
    (hammingDist a b : ℝ) =
    ∑ i : Fin d, if (a i ^^ b i) = true then (1:ℝ) else 0 := by
  unfold hammingDist; rw [Finset.card_filter]; push_cast; congr 1; ext i
  cases (a i) <;> cases (b i) <;> simp [Bool.xor]

/-- Translates the "low Hamming distance" event into a lower-tail event on the sum of centered
XOR indicators: `hamming a b < (1/2 - γ) d` iff `∑ boolCenter (a ⊕ b) < -γ d`. -/
lemma hammingDist_lt_iff_boolCenter_xor {d : ℕ} {γ : ℝ} (a b : Fin d → Bool) :
    (hammingDist a b : ℝ) < (1/2 - γ) * ↑d ↔
    (∑ i : Fin d, boolCenter ((fun i => a i ^^ b i) i) : ℝ) < -(γ * ↑d) := by
  have hkey : (hammingDist a b : ℝ) =
      (∑ i : Fin d, boolCenter ((fun i => a i ^^ b i) i)) + (d:ℝ) / 2 := by
    rw [hammingDist_cast_eq', boolCenter_sum_eq_weight]; ring
  rw [hkey]; constructor <;> intro h <;> linarith

/-- Hoeffding-type bound on the number of pairs `(a, b) ∈ (Fin d → Bool)²` with Hamming distance
below `(1/2 - γ) d`: at most `exp(-2 γ² d) · 4^d`. -/
lemma hoeffding_pair_level_bound {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ_pos : 0 < γ)
    (hγ_lt : γ < 1/2) :
    (((Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter
      fun p => (hammingDist p.1 p.2 : ℝ) < (1/2 - γ) * ↑d).card : ℝ)
    ≤ Real.exp (-(2 * γ ^ 2 * ↑d)) *
      ↑(Fintype.card ((Fin d → Bool) × (Fin d → Bool))) := by


  set μ := Measure.pi (fun (_ : Fin d) => μ_Bool) with μ_def
  set X : Fin d → (Fin d → Bool) → ℝ := fun i ω => boolCenter (ω i) with X_def
  have hγd_pos : 0 < γ * ↑d := mul_pos hγ_pos (Nat.cast_pos.mpr hd)

  have hoeff := hoeffding_sum_lower_tail
    (n := d) (X := X) (a := fun _ => -(1 : ℝ)/2) (b := fun _ => (1 : ℝ)/2)
    (fun _ => by norm_num)
    (fun _ => Measurable.of_discrete)
    (fun _ => Integrable.of_finite)
    (fun _ => Filter.Eventually.of_forall fun ω => by
      simp only [X_def, boolCenter]; split <;> norm_num)
    (fun _ => Filter.Eventually.of_forall fun ω => by
      simp only [X_def, boolCenter]; split <;> norm_num)
    (fun i => mean_boolCenter_coord_zero d i)
    (indep_boolCenter_coords d)
    (γ * ↑d) hγd_pos

  have exp_eq : -(2 * (γ * ↑d) ^ 2 / ∑ _ : Fin d, ((1 : ℝ) / 2 - -(1 : ℝ) / 2) ^ 2)
      = -(2 * γ ^ 2 * ↑d) := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    field_simp; ring
  rw [exp_eq] at hoeff


  have hμ_singleton : ∀ (ω : Fin d → Bool), μ {ω} = (1 / 2 : ENNReal) ^ d := by
    intro ω
    rw [μ_def, show ({ω} : Set (Fin d → Bool)) = Set.univ.pi (fun i => {ω i}) from by
      ext x; simp [Set.mem_pi, funext_iff]]
    rw [Measure.pi_pi]
    simp only [μ_Bool_singleton, Finset.prod_const, Finset.card_fin]

  have hμ_set : ∀ (S : Finset (Fin d → Bool)),
      μ (↑S : Set (Fin d → Bool)) = ↑S.card * (1 / 2 : ENNReal) ^ d := by
    intro S
    rw [show (↑S : Set (Fin d → Bool)) = ⋃ (x : S), {(x : Fin d → Bool)} from by
      ext y; simp [Finset.mem_coe]]
    rw [measure_iUnion (fun i j hij => by simp [Subtype.val_injective.ne hij])
        (fun _ => measurableSet_singleton _)]
    simp only [hμ_singleton, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_coe]


  set badStrFin := (Finset.univ : Finset (Fin d → Bool)).filter
    fun c => (∑ i : Fin d, boolCenter (c i) : ℝ) < -((γ : ℝ) * ↑d)

  have h_event_eq : {ω : Fin d → Bool | ∑ i, X i ω < -(γ * ↑d)} =
      ↑badStrFin := by
    ext ω
    simp only [X_def, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, badStrFin]

  rw [h_event_eq] at hoeff

  have hμ_bad := hμ_set badStrFin


  have h_card_Bd : Fintype.card (Fin d → Bool) = 2 ^ d := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

  have h2d_pos : (0 : ℝ) < 2 ^ d := pow_pos (by norm_num : (0:ℝ) < 2) d
  have h2d_ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2d_pos

  have h_bad_le : (badStrFin.card : ℝ) ≤ exp (-(2 * γ ^ 2 * ↑d)) * (2 : ℝ) ^ d := by


    have h1 : (↑badStrFin.card : ENNReal) * (1 / 2) ^ d ≤
        ENNReal.ofReal (exp (-(2 * γ ^ 2 * ↑d))) := hμ_bad ▸ hoeff

    rw [ENNReal.le_ofReal_iff_toReal_le
        (ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) (hμ_bad ▸ hoeff))
        (le_of_lt (exp_pos _))] at h1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h1

    calc (badStrFin.card : ℝ)
        = badStrFin.card * ((1/2)^d * 2^d) := by rw [one_div, inv_pow, inv_mul_cancel₀ h2d_ne]; ring
      _ = badStrFin.card * (1/2)^d * 2^d := by ring
      _ ≤ exp (-(2 * γ ^ 2 * ↑d)) * 2 ^ d :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt h2d_pos)


  have h_pair_le_prod : ((Finset.univ.filter
      fun p : (Fin d → Bool) × (Fin d → Bool) =>
        (hammingDist p.1 p.2 : ℝ) < (1/2 - γ) * ↑d).card : ℝ) ≤
      ↑badStrFin.card * ↑(Fintype.card (Fin d → Bool)) := by

    set badPairs := Finset.univ.filter (fun p : (Fin d → Bool) × (Fin d → Bool) =>
      (hammingDist p.1 p.2 : ℝ) < (1/2 - γ) * ↑d)
    set prod := (badStrFin ×ˢ (Finset.univ : Finset (Fin d → Bool)))
    set f : (Fin d → Bool) × (Fin d → Bool) → (Fin d → Bool) × (Fin d → Bool) :=
      fun p => (fun i => p.1 i ^^ p.2 i, p.1)
    have hf_maps : Set.MapsTo f ↑badPairs ↑prod := by
      intro ⟨a, b⟩ hx
      simp only [badPairs, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
      simp only [prod, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hammingDist_lt_iff_boolCenter_xor a b).mp hx⟩
    have hf_inj : Set.InjOn f ↑badPairs := by
      intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨hxor, ha⟩ := h
      exact Prod.ext ha (funext fun i => by
        have := congr_fun hxor i; simp only at this; subst ha; cases a₁ i <;> simp_all)
    have h_card := Finset.card_le_card_of_injOn f hf_maps hf_inj
    have h_prod_card : prod.card = badStrFin.card * Fintype.card (Fin d → Bool) := by
      simp only [prod, Finset.card_product, Finset.card_univ]
    rw [h_prod_card] at h_card
    exact_mod_cast h_card


  calc (((Finset.univ : Finset ((Fin d → Bool) × (Fin d → Bool))).filter
        fun p => (hammingDist p.1 p.2 : ℝ) < (1/2 - γ) * ↑d).card : ℝ)
      ≤ ↑badStrFin.card * ↑(Fintype.card (Fin d → Bool)) := h_pair_le_prod
    _ ≤ (exp (-(2 * γ ^ 2 * ↑d)) * 2 ^ d) * ↑(Fintype.card (Fin d → Bool)) := by
        apply mul_le_mul_of_nonneg_right h_bad_le; exact Nat.cast_nonneg _
    _ = exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card ((Fin d → Bool) × (Fin d → Bool))) := by
        rw [Fintype.card_prod, h_card_Bd]
        push_cast [Nat.cast_pow]
        ring

/-- Lift the pairwise Hoeffding bound to families: among configurations `ω : Fin M → (Fin d → Bool)`,
the number with `hammingDist (ω j) (ω k) < (1/2 - γ) d` is at most `exp(-2 γ² d)` times the total
count. -/
theorem hoeffding_pair_count_bound {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ_pos : 0 < γ)
    (hγ_lt : γ < 1/2) {M : ℕ} (j k : Fin M) (hjk : j ≠ k) :
    (((Finset.univ : Finset (Fin M → (Fin d → Bool))).filter
      fun ω => (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d).card : ℝ)
    ≤ Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card (Fin M → (Fin d → Bool))) := by
  set α := Fin d → Bool with α_def
  set R := {i : Fin M // i ∉ ({j, k} : Finset (Fin M))} → α with R_def
  set e := fiberEquiv j k hjk α
  set P : α × α → Prop := fun p => (hammingDist p.1 p.2 : ℝ) < (1/2 - γ) * ↑d with P_def

  rw [show ((Finset.univ.filter fun ω : Fin M → α =>
    (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d).card : ℝ) =
    (Fintype.card {ω : Fin M → α // P (ω j, ω k)} : ℝ) from by
      push_cast; congr 1; rw [← Fintype.subtype_card]]

  have card_filt_eq : Fintype.card {ω : Fin M → α // P (ω j, ω k)} =
      Fintype.card {p : α × α // P p} * Fintype.card R := by
    have eq1 : Fintype.card {ω : Fin M → α // P (ω j, ω k)} =
        Fintype.card {q : (α × α) × R // P q.1} :=
      Fintype.card_congr ((Equiv.subtypeEquiv e) fun ω => by
        have h := fiberEquiv_fst j k hjk α ω
        constructor <;> intro hh <;> [rwa [h]; rwa [← h]])
    rw [eq1, Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := P)),
      Fintype.card_prod]

  have card_total_eq : Fintype.card (Fin M → α) =
      Fintype.card (α × α) * Fintype.card R :=
    (Fintype.card_congr e).trans (Fintype.card_prod _ _)

  have pair_bound : (Fintype.card {p : α × α // P p} : ℝ) ≤
      Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card (α × α)) := by
    have h := hoeffding_pair_level_bound hd hγ_pos hγ_lt
    rwa [← Fintype.subtype_card] at h

  calc (Fintype.card {ω : Fin M → α // P (ω j, ω k)} : ℝ)
      = ↑(Fintype.card {p : α × α // P p} * Fintype.card R) := by rw [card_filt_eq]
    _ = ↑(Fintype.card {p : α × α // P p}) * ↑(Fintype.card R) := by push_cast; ring
    _ ≤ (Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card (α × α))) * ↑(Fintype.card R) :=
        mul_le_mul_of_nonneg_right pair_bound (Nat.cast_nonneg _)
    _ = Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card (α × α) * Fintype.card R) := by
        push_cast; ring
    _ = Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑(Fintype.card (Fin M → α)) := by
        rw [← card_total_eq]

/-- Twice the count of strictly increasing pairs in `Fin M × Fin M` is at most the cardinality of
the off-diagonal. -/
lemma two_mul_card_lt_pairs_le_offDiag (M : ℕ) :
    2 * ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2)).card ≤
    (Finset.univ : Finset (Fin M)).offDiag.card := by
  have h_eq :
    ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2)).card =
    ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.2 < p.1)).card := by
    apply Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) <;>
    intro ⟨j, k⟩ hjk <;> simp_all [Finset.mem_filter]
  have h_disj : Disjoint
    ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2))
    ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_filter]
    intro ⟨j, k⟩ _ hlt hgt; exact Nat.lt_asymm hlt hgt
  have h_sub : (Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2) ∪
    (Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.2 < p.1) ⊆
    (Finset.univ : Finset (Fin M)).offDiag := by
    intro ⟨j, k⟩ hjk
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hjk
    rw [Finset.mem_offDiag]
    rcases hjk with h | h
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, Fin.ne_of_lt h⟩
    · exact ⟨Finset.mem_univ _, Finset.mem_univ _, (Fin.ne_of_lt h).symm⟩
  have h1 := Finset.card_le_card h_sub
  rw [Finset.card_union_of_disjoint h_disj] at h1; omega

/-- Union-bound count: if `M (M-1) < 2 · exp(2 γ² d)`, then the number of configurations
`ω : Fin M → (Fin d → Bool)` admitting some pair with Hamming distance below `(1/2 - γ) d`
is strictly less than the total number of configurations. -/
theorem hoeffding_union_bound_count (d : ℕ) (hd : 0 < d)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1/2) (M : ℕ) (hM : 1 < M)
    (hM_bound : (M : ℝ) * ((M : ℝ) - 1) < 2 * Real.exp (2 * γ ^ 2 * ↑d)) :
    ((Finset.univ : Finset (Fin M → (Fin d → Bool))).filter
      fun ω => ∃ j k : Fin M, j ≠ k ∧ (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d).card <
    Fintype.card (Fin M → (Fin d → Bool)) := by
  set T := Fintype.card (Fin M → (Fin d → Bool)) with hT_def
  set badSet := (Finset.univ : Finset (Fin M → (Fin d → Bool))).filter
    (fun ω => ∃ j k : Fin M, j ≠ k ∧ (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d)
  set ltPairs := ((Finset.univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2))
  set perPair := fun (p : Fin M × Fin M) => (Finset.univ : Finset (Fin M → (Fin d → Bool))).filter
    (fun ω => (hammingDist (ω p.1) (ω p.2) : ℝ) < (1/2 - γ) * ↑d)

  suffices h : (badSet.card : ℝ) < (T : ℝ) by exact_mod_cast h
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos

  have h_sub : badSet ⊆ ltPairs.biUnion perPair := by
    intro ω hω
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    obtain ⟨j, k, hjk, hbad⟩ := hω
    rw [Finset.mem_biUnion]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjk) with h | h
    · exact ⟨⟨j, k⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
    · refine ⟨⟨k, j⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [hammingDist_symm]; exact hbad

  have h_ub : (badSet.card : ℝ) ≤ ∑ p ∈ ltPairs, ((perPair p).card : ℝ) := by
    have : badSet.card ≤ ∑ p ∈ ltPairs, (perPair p).card :=
      (Finset.card_le_card h_sub).trans Finset.card_biUnion_le
    exact_mod_cast this

  have h_per : ∀ p ∈ ltPairs, ((perPair p).card : ℝ) ≤ Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑T := by
    intro ⟨j, k⟩ hp
    simp only [ltPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hoeffding_pair_count_bound hd hγ_pos hγ_lt j k (Fin.ne_of_lt hp)

  have h_sum : ∑ p ∈ ltPairs, ((perPair p).card : ℝ) ≤
      ↑ltPairs.card * (Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑T) := by
    have := Finset.sum_le_card_nsmul _ _ _ h_per
    simp only [nsmul_eq_mul] at this; exact this

  have h_card_real : (ltPairs.card : ℝ) * 2 ≤ (M : ℝ) * ((M : ℝ) - 1) := by
    have h_nat := two_mul_card_lt_pairs_le_offDiag M
    have h_off : (Finset.univ : Finset (Fin M)).offDiag.card = M * M - M := by
      rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    rw [h_off] at h_nat
    have hMM : M ≤ M * M := Nat.le_mul_of_pos_left M (by omega)
    have h' : (2 * ltPairs.card : ℝ) ≤ ((M * M - M : ℕ) : ℝ) := by exact_mod_cast h_nat
    rw [Nat.cast_sub hMM] at h'
    push_cast at h' ⊢; linarith

  have h_n_lt : (ltPairs.card : ℝ) * 2 < 2 * Real.exp (2 * γ ^ 2 * ↑d) := by linarith
  have hexp_pos : 0 < Real.exp (2 * γ ^ 2 * ↑d) := Real.exp_pos _
  have h_n_lt' : (ltPairs.card : ℝ) < Real.exp (2 * γ ^ 2 * ↑d) := by linarith

  have h_prod_lt : (ltPairs.card : ℝ) * Real.exp (-(2 * γ ^ 2 * ↑d)) < 1 := by
    rw [Real.exp_neg, mul_inv_lt_iff₀ hexp_pos]; linarith

  calc (badSet.card : ℝ) ≤ ∑ p ∈ ltPairs, ((perPair p).card : ℝ) := h_ub
    _ ≤ ↑ltPairs.card * (Real.exp (-(2 * γ ^ 2 * ↑d)) * ↑T) := h_sum
    _ = (↑ltPairs.card * Real.exp (-(2 * γ ^ 2 * ↑d))) * ↑T := by ring
    _ < 1 * ↑T := by nlinarith
    _ = ↑T := by ring

/-- Probabilistic-method version of Varshamov-Gilbert: under the same count condition, there
exists a configuration `ω : Fin M → (Fin d → Bool)` whose pairwise Hamming distances are all at
least `(1/2 - γ) d`. -/
lemma probabilistic_method_separated_vectors (d : ℕ) (hd : 0 < d)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1/2) (M : ℕ) (hM : 0 < M)
    (hM_bound : (M : ℝ) * ((M : ℝ) - 1) < 2 * Real.exp (2 * γ ^ 2 * ↑d)) :
    ∃ (ω : Fin M → (Fin d → Bool)),
    ∀ j k : Fin M, j ≠ k →
      (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - γ) * ↑d := by

  by_cases hM1 : M = 1
  · subst hM1
    exact ⟨fun _ _ => false, fun j k hjk => absurd (Fin.ext (by omega)) hjk⟩


  have hM2 : 1 < M := by omega
  have h_bad := hoeffding_union_bound_count d hd γ hγ_pos hγ_lt M hM2 hM_bound

  have h_ne_univ : (Finset.univ : Finset (Fin M → (Fin d → Bool))).filter
      (fun ω => ∃ j k : Fin M, j ≠ k ∧ (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d) ≠
      Finset.univ := by
    intro h_eq; rw [h_eq, Finset.card_univ] at h_bad; exact Nat.lt_irrefl _ h_bad

  have h_good : ∃ ω : Fin M → (Fin d → Bool),
      ¬(∃ j k : Fin M, j ≠ k ∧ (hammingDist (ω j) (ω k) : ℝ) < (1/2 - γ) * ↑d) := by
    by_contra hall
    push Not at hall
    exact h_ne_univ (Finset.filter_true_of_mem (fun x _ => hall x))
  obtain ⟨ω, hω⟩ := h_good
  push Not at hω
  exact ⟨ω, fun j k hjk => hω j k hjk⟩

/-- **Varshamov-Gilbert theorem.** For any dimension `d ≥ 1` and any `0 < γ < 1/2`, there exist
`M ≥ exp(γ² d / 2)` Boolean vectors in `{0,1}^d` with pairwise Hamming distance at least
`(1/2 - γ) d`. -/
theorem varshamov_gilbert (d : ℕ) (hd : 0 < d)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt : γ < 1/2) :
    ∃ (M : ℕ) (hM : 0 < M) (ω : Fin M → (Fin d → Bool)),
    (M : ℝ) ≥ Real.exp (γ ^ 2 * d / 2) ∧
    ∀ j k : Fin M, j ≠ k →
      (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - γ) * d := by

  set s := γ ^ 2 * (d : ℝ) / 2 with hs_def
  set M := ⌈Real.exp s⌉₊ with hM_def
  have hs_pos : 0 < s := by positivity
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos s)
  have hM_ge2 : 2 ≤ M :=
    Nat.lt_ceil.mpr (by exact_mod_cast Real.one_lt_exp_iff.mpr hs_pos)
  have hM_ge_real : (M : ℝ) ≥ Real.exp s := Nat.le_ceil (Real.exp s)
  have hM_lt : (M : ℝ) < Real.exp s + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos s))
  have hM_ge2_real : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge2


  have hs_eq : 4 * s = 2 * γ ^ 2 * ↑d := by rw [hs_def]; ring
  have hM_bound : (M : ℝ) * ((M : ℝ) - 1) < 2 * Real.exp (2 * γ ^ 2 * ↑d) := by
    have hM_sub_lt : (M : ℝ) - 1 < Real.exp s := by linarith
    have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by linarith
    have hM_sub_nonneg : (0 : ℝ) ≤ (M : ℝ) - 1 := by linarith
    have step1 : (M : ℝ) * ((M : ℝ) - 1) < (Real.exp s + 1) * Real.exp s :=
      mul_lt_mul'' hM_lt hM_sub_lt hM_nonneg hM_sub_nonneg
    have step2 : (Real.exp s + 1) * Real.exp s = Real.exp (2 * s) + Real.exp s := by
      rw [add_mul, ← Real.exp_add]; ring_nf
    have step3 : Real.exp s < Real.exp (2 * s) := Real.exp_strictMono (by linarith)
    have step4 : 2 * s < 4 * s := by linarith
    have step5 : Real.exp (2 * s) ≤ Real.exp (4 * s) :=
      le_of_lt (Real.exp_strictMono step4)
    rw [← hs_eq]
    linarith

  obtain ⟨ω, hω⟩ := probabilistic_method_separated_vectors d hd γ hγ_pos hγ_lt M hM_pos hM_bound
  exact ⟨M, hM_pos, ω, hM_ge_real, hω⟩

/-- The `ℓ⁰`-norm of a Boolean vector: the number of coordinates equal to `true`. -/
def l0norm_bool {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

/-- **Sparse Varshamov-Gilbert theorem.** For `1 ≤ k ≤ d/8`, there exist `M ≥ 5` Boolean vectors,
each of weight exactly `k`, with pairwise Hamming distance at least `k/2` and
`log M ≥ (k/8) · log(1 + d/(2k))`. -/
theorem sparse_varshamov_gilbert (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d / 8) :
    ∃ (M : ℕ) (hM : 0 < M) (ω : Fin M → (Fin d → Bool)),
    Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧
    5 ≤ M ∧
    (∀ j : Fin M, l0norm_bool (ω j) = k) ∧
    ∀ j k' : Fin M, j ≠ k' → (hammingDist (ω j) (ω k') : ℝ) ≥ (k : ℝ) / 2 := by

  obtain ⟨M, hM_pos, ω, hM8, hlog, hweight, hdist⟩ :=
    SparseVarshamovGilbert.sparse_vg_card_bound d k hk hkd
  refine ⟨M, hM_pos, ω, hlog, by omega, ?_, ?_⟩
  ·
    intro j; exact hweight j
  ·
    intro j k' hjk
    show (↑(hammingDist (ω j) (ω k')) : ℝ) ≥ (↑k : ℝ) / 2
    have heq : hammingDist (ω j) (ω k') = SparseVarshamovGilbert.hammingDist (ω j) (ω k') := by
      simp only [hammingDist, SparseVarshamovGilbert.hammingDist]
    rw [heq]
    exact hdist j k' hjk

/-- The squared Euclidean distance `sqDist x y = ∑ (x i - y i)²` is nonnegative. -/
theorem sqDist_nonneg {d : ℕ} (x y : Fin d → ℝ) : sqDist x y ≥ 0 := by
  unfold sqDist
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- **Markov-style lower bound.** If `f ≥ 0` and `P(f ≥ ϕ) ≥ p`, then `p ϕ ≤ ∫ f dμ`. -/
theorem markov_step
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (ϕ p : ℝ)
    (hϕ : 0 < ϕ) (hp : 0 < p)
    (hnn : ∀ ω, f ω ≥ 0)
    (hint : Integrable f μ)
    (hprob : (μ {ω | f ω ≥ ϕ}).toReal ≥ p) :
    p * ϕ ≤ ∫ ω, f ω ∂μ := by
  calc p * ϕ
      ≤ μ.real {x | ϕ ≤ f x} * ϕ :=
        mul_le_mul_of_nonneg_right hprob (le_of_lt hϕ)
    _ = ϕ * μ.real {x | ϕ ≤ f x} := mul_comm _ _
    _ ≤ ∫ ω, f ω ∂μ :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hnn) hint ϕ

/-- **Markov bridge (strong form).** Bridges a pointwise lower bound on
`P_θ(sqDist (θhat Y) θ ≥ ϕ) ≥ p` to a minimax risk bound
`infθhat supθ ∫ sqDist (θhat Y) θ ≥ p ϕ`. -/
theorem markov_bridge_strong
    {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ))
    (ϕ p : ℝ) (hϕ : 0 < ϕ) (hp : 0 < p)
    (hint : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → Integrable (fun Y => sqDist (θhat Y) θ) (P θ))
    (hmeas : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → AEStronglyMeasurable (fun Y => sqDist (θhat Y) θ) (P θ))
    (hbdd : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ), ∫ Y, sqDist (θhat Y) θ ∂(P θ)))
    (hprob : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      ∃ θ ∈ Θ, (P θ {Y | sqDist (θhat Y) θ ≥ ϕ}).toReal ≥ p) :
    ⨅ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      ⨆ θ ∈ Θ, ∫ Y, sqDist (θhat Y) θ ∂(P θ) ≥ p * ϕ := by
  rw [ge_iff_le]
  apply le_ciInf
  intro θhat
  obtain ⟨θ₀, hθ₀mem, hθ₀prob⟩ := hprob θhat


  have h_integral : p * ϕ ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂(P θ₀) :=
    markov_step (P θ₀) (fun Y => sqDist (θhat Y) θ₀) ϕ p hϕ hp
      (fun Y => sqDist_nonneg (θhat Y) θ₀) (hint θhat θ₀ hθ₀mem) hθ₀prob

  calc p * ϕ
      ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂(P θ₀) := h_integral
    _ ≤ ⨆ θ ∈ Θ, ∫ Y, sqDist (θhat Y) θ ∂(P θ) := by
        apply le_ciSup_of_le (hbdd θhat) θ₀


        have hbdd_inner : BddAbove (Set.range fun (_ : θ₀ ∈ Θ) =>
            ∫ Y, sqDist (θhat Y) θ₀ ∂(P θ₀)) :=
          ⟨∫ Y, sqDist (θhat Y) θ₀ ∂(P θ₀), by rintro _ ⟨_, rfl⟩; exact le_refl _⟩
        exact le_ciSup hbdd_inner hθ₀mem

/-- Convenience wrapper around `markov_bridge_strong` exposing the same Markov-style minimax
lower bound. -/
theorem markov_bridge
    {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ))
    (ϕ p : ℝ) (hϕ : 0 < ϕ) (hp : 0 < p)
    (hint : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → Integrable (fun Y => sqDist (θhat Y) θ) (P θ))
    (hmeas : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
      θ ∈ Θ → AEStronglyMeasurable (fun Y => sqDist (θhat Y) θ) (P θ))
    (hbdd : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ), ∫ Y, sqDist (θhat Y) θ ∂(P θ)))
    (hprob : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      ∃ θ ∈ Θ, (P θ {Y | sqDist (θhat Y) θ ≥ ϕ}).toReal ≥ p) :
    ⨅ (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
      ⨆ θ ∈ Θ, ∫ Y, sqDist (θhat Y) θ ∂(P θ) ≥ p * ϕ :=
  markov_bridge_strong P Θ ϕ p hϕ hp hint hmeas hbdd hprob

/-- The Hamming distance from `ω₀` to `ω` equals the Hamming weight (distance from `0`) of
their XOR. -/
lemma hammingDist_xor_eq {d : ℕ} (ω₀ ω : Fin d → Bool) :
    hammingDist ω₀ ω = hammingDist (fun _ => false) (fun i => ω₀ i ^^ ω i) := by
  unfold hammingDist
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases ω₀ i <;> cases ω i <;> simp

/-- Pointwise version of XOR self-cancellation: `ω₀ ^^ (ω₀ ^^ ω) = ω`. -/
lemma xor_self_cancel {d : ℕ} (ω₀ ω : Fin d → Bool) :
    (fun i => ω₀ i ^^ (ω₀ i ^^ ω i)) = ω := by
  ext i; cases ω₀ i <;> cases ω i <;> simp

/-- Translation invariance for Hamming balls: the cardinality of an open ball of radius
`(1/2 - 1/4) d` around any center `ω₀` equals that of the ball around the zero vector. -/
lemma hamming_ball_card_eq_zero_center {d : ℕ} (ω₀ : Fin d → Bool) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d).card =
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d).card := by
  apply Finset.card_nbij' (fun ω i => ω₀ i ^^ ω i) (fun ω i => ω₀ i ^^ ω i)
  · intro ω hω
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rwa [hammingDist_xor_eq] at hω
  · intro ω hω
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    have : hammingDist ω₀ (fun i => ω₀ i ^^ ω i) = hammingDist (fun _ => false) ω := by
      rw [hammingDist_xor_eq]; congr 1; exact xor_self_cancel ω₀ ω
    rwa [this]
  · intro ω _; exact xor_self_cancel ω₀ ω
  · intro ω _; exact xor_self_cancel ω₀ ω

/-- Tilting identity: `∑_{ω ∈ {0,1}^d} 3^(d - |ω|) = 4^d`, used in Chernoff-style ball-volume
bounds via a binomial-expansion argument. -/
lemma tilting_identity (d : ℕ) :
    ∑ ω : Fin d → Bool, 3 ^ (d - hammingDist (fun _ => false) ω) = 4 ^ d := by
  have h4 : (4 : ℕ) = ∑ b : Bool, (if b = true then 1 else 3) := by simp
  rw [h4, Fintype.sum_pow]
  congr 1; ext ω
  have hwt : hammingDist (fun _ => false) ω =
      (Finset.univ.filter fun i : Fin d => ω i = true).card := by
    unfold hammingDist
    congr 1; ext i
    constructor <;> intro h <;> (cases ω i <;> simp_all)
  rw [hwt]
  symm
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp [Finset.card_univ]


/-- Numerical bound: `e < 87/32`. -/
lemma _exp_one_lt : Real.exp (1 : ℝ) < 87/32 := by
  have hb := Real.exp_bound' (show (0:ℝ) ≤ 1 by positivity) (le_refl (1:ℝ)) (show 0 < 10 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb; norm_num at hb ⊢; linarith

/-- Numerical bound: `exp(1/2) < 27/16`. -/
lemma _exp_half_lt : Real.exp (1/2 : ℝ) < 27/16 := by
  have h1 := Real.exp_bound' (show (0:ℝ) ≤ 1/2 by positivity) (show (1/2:ℝ) ≤ 1 by norm_num) (show 0 < 5 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1; norm_num at h1 ⊢; linarith

/-- Numerical bound: `exp(2) < 7569/1024`. -/
lemma _exp_two_lt : Real.exp (2 : ℝ) < 7569/1024 := by
  rw [show (2:ℝ) = ↑(2:ℕ)*1 from by norm_num, Real.exp_nat_mul]
  calc Real.exp 1 ^ 2 < (87/32)^2 := pow_lt_pow_left₀ _exp_one_lt (Real.exp_pos 1).le (by omega)
    _ = 7569/1024 := by norm_num

/-- Numerical bound: `exp(3/8) < 3/2`. -/
lemma _exp_three_eighths_lt : Real.exp (3/8 : ℝ) < 3/2 := by
  have hb := Real.exp_bound' (show (0:ℝ) ≤ 3/8 by positivity) (show (3/8:ℝ) ≤ 1 by norm_num) (show 0 < 5 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb; norm_num at hb ⊢; linarith

/-- Numerical bound: `exp(5/8) < 15/8`. -/
lemma _exp_five_eighths_lt : Real.exp (5/8 : ℝ) < 15/8 := by
  have hb := Real.exp_bound' (show (0:ℝ) ≤ 5/8 by positivity) (show (5/8:ℝ) ≤ 1 by norm_num) (show 0 < 5 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb; norm_num at hb ⊢; linarith

/-- Numerical bound: `exp(3/4) < 17/8`. -/
lemma _exp_three_quarters_lt : Real.exp (3/4 : ℝ) < 17/8 := by
  have hb := Real.exp_bound' (show (0:ℝ) ≤ 3/4 by positivity) (show (3/4:ℝ) ≤ 1 by norm_num) (show 0 < 5 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb; norm_num at hb ⊢; linarith

/-- Numerical bound: `exp(1/4) < 13/10`. -/
lemma _exp_quarter_lt : Real.exp ((1:ℝ)/4) < 13/10 := by
  have hb := Real.exp_bound' (show (0:ℝ) ≤ 1/4 by positivity) (show (1/4:ℝ) ≤ 1 by norm_num) (show 0 < 5 by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb; norm_num at hb ⊢; linarith


/-- Base case `d = 19` of the induction `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_base_19 : (2:ℝ)^19 * (Real.exp (19/8) + 1) < (3:ℝ)^15 := by
  have hexp : Real.exp ((19:ℝ)/8) < 22707/2048 := by
    rw [show (19:ℝ)/8 = 2 + 3/8 from by norm_num, Real.exp_add]
    nlinarith [_exp_two_lt, _exp_three_eighths_lt, Real.exp_pos (2:ℝ), Real.exp_pos (3/8:ℝ)]
  norm_num; nlinarith

/-- Base case `d = 20` of the induction `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_base_20 : (2:ℝ)^20 * (Real.exp (20/8) + 1) < (3:ℝ)^15 := by
  have hexp : Real.exp ((20:ℝ)/8) < 204363/16384 := by
    rw [show (20:ℝ)/8 = 2 + 1/2 from by norm_num, Real.exp_add]
    nlinarith [_exp_two_lt, _exp_half_lt, Real.exp_pos (2:ℝ), Real.exp_pos (1/2:ℝ)]
  norm_num; nlinarith

/-- Base case `d = 21` of the induction `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_base_21 : (2:ℝ)^21 * (Real.exp (21/8) + 1) < (3:ℝ)^16 := by
  have hexp : Real.exp ((21:ℝ)/8) < 113535/8192 := by
    rw [show (21:ℝ)/8 = 2 + 5/8 from by norm_num, Real.exp_add]
    nlinarith [_exp_two_lt, _exp_five_eighths_lt, Real.exp_pos (2:ℝ), Real.exp_pos (5/8:ℝ)]
  norm_num; nlinarith

/-- Base case `d = 22` of the induction `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_base_22 : (2:ℝ)^22 * (Real.exp (22/8) + 1) < (3:ℝ)^17 := by
  have hexp : Real.exp ((22:ℝ)/8) < 128673/8192 := by
    rw [show (22:ℝ)/8 = 2 + 3/4 from by norm_num, Real.exp_add]
    nlinarith [_exp_two_lt, _exp_three_quarters_lt, Real.exp_pos (2:ℝ), Real.exp_pos (3/4:ℝ)]
  norm_num; nlinarith


/-- Inductive step (`d ↦ d + 4`) of `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_step (d : ℕ) (hd : 19 ≤ d)
    (ih : (2 : ℝ)^d * (Real.exp (↑d/8) + 1) < (3 : ℝ)^(d - d/4)) :
    (2 : ℝ)^(d+4) * (Real.exp (↑(d+4)/8) + 1) < (3 : ℝ)^((d+4) - (d+4)/4) := by
  rw [show (d + 4) / 4 = d / 4 + 1 from by omega]
  rw [show d + 4 - (d / 4 + 1) = d - d / 4 + 3 from by omega]
  rw [show (↑(d + 4) : ℝ) / 8 = ↑d / 8 + 1 / 2 from by push_cast; ring]
  rw [Real.exp_add]
  have h2d : (0 : ℝ) < 2^d := by positivity
  have key : 16 * (Real.exp (1/2) * Real.exp (↑d / 8) + 1) < 27 * (Real.exp (↑d / 8) + 1) := by
    nlinarith [_exp_half_lt, Real.exp_pos (↑d / 8)]
  have step1 : 16 * (2:ℝ)^d * (Real.exp (1/2) * Real.exp (↑d / 8) + 1) <
      27 * (2:ℝ)^d * (Real.exp (↑d / 8) + 1) := by nlinarith
  linarith [show (2:ℝ)^(d+4) * (Real.exp (↑d / 8) * Real.exp (1/2) + 1) =
      16 * (2:ℝ)^d * (Real.exp (1/2) * Real.exp (↑d / 8) + 1) from by ring,
    show (3:ℝ)^(d - d/4 + 3) = 27 * (3:ℝ)^(d - d/4) from by ring]


/-- For all `d ≥ 19`, `2^d (exp(d/8) + 1) < 3^(d - d/4)`. -/
lemma _real_ineq_large (d : ℕ) (hd : 19 ≤ d) :
    (2 : ℝ)^d * (Real.exp (↑d/8) + 1) < (3 : ℝ)^(d - d/4) := by
  induction d using Nat.strongRecOn with
  | _ d ih =>
    by_cases hd22 : d ≤ 22
    · interval_cases d
      · exact _real_ineq_base_19
      · exact _real_ineq_base_20
      · exact _real_ineq_base_21
      · exact _real_ineq_base_22
    · push Not at hd22
      have ihm := ih (d - 4) (by omega) (by omega : 19 ≤ d - 4)
      rw [← show d - 4 + 4 = d from by omega]
      exact _real_ineq_step (d - 4) (by omega) ihm


/-- Integer form of the large-`d` inequality: `2^d · ⌈exp(d/8)⌉ < 3^(d - d/4)` for `d ≥ 19`. -/
lemma _nat_ineq_large (d : ℕ) (hd : 19 ≤ d) :
    2^d * ⌈Real.exp (↑d / 8)⌉₊ < 3^(d - d/4) := by
  have hreal := _real_ineq_large d hd
  have hceil : (⌈Real.exp (↑d / 8)⌉₊ : ℝ) ≤ Real.exp (↑d / 8) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos (↑d / 8 : ℝ)).le)
  suffices h : (2:ℝ)^d * ↑⌈Real.exp (↑d / 8)⌉₊ < (3:ℝ)^(d - d/4) by exact_mod_cast h
  calc (2:ℝ)^d * ↑⌈Real.exp (↑d / 8)⌉₊ ≤ (2:ℝ)^d * (Real.exp (↑d / 8) + 1) :=
        mul_le_mul_of_nonneg_left hceil (by positivity)
    _ < (3:ℝ)^(d - d/4) := hreal


/-- Chernoff-style ball volume bound (real version): the number of Boolean vectors with weight
strictly less than `d/4` times `3^(d - d/4)` is at most `4^d`. -/
lemma _tilting_real_ball_bound (d : ℕ) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d).card * 3^(d - d/4) ≤ 4^d := by
  set S := Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d
  have htilt := tilting_identity d
  rw [show S.card * 3^(d - d/4) = ∑ _ω ∈ S, 3^(d - d/4) from by rw [Finset.sum_const, smul_eq_mul]]
  calc ∑ _ω ∈ S, 3^(d - d/4)
      ≤ ∑ ω ∈ S, 3^(d - hammingDist (fun _ => false) ω) := by
        apply Finset.sum_le_sum; intro ω hω
        apply Nat.pow_le_pow_right (by omega : 0 < 3)
        have hωS : (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hω; exact hω
        have : 4 * hammingDist (fun _ => false) ω < d := by
          exact_mod_cast (show (4 * hammingDist (fun _ => false) ω : ℝ) < d by nlinarith)
        omega
    _ ≤ ∑ ω : Fin d → Bool, 3^(d - hammingDist (fun _ => false) ω) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 4^d := htilt


/-- For `d ≥ 19`, `⌈exp(d/8)⌉ ≥ 3`. -/
lemma _ceil_exp_ge_three (d : ℕ) (hd : 19 ≤ d) : 3 ≤ ⌈Real.exp (↑d / 8)⌉₊ := by
  have hle : (↑d : ℝ) / 8 + 1 ≤ Real.exp (↑d / 8) := Real.add_one_le_exp _
  have hge : (3 : ℝ) ≤ (↑d : ℝ) / 8 + 1 := by
    have hd19 : (19 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h3 : (3 : ℝ) ≤ ↑(⌈Real.exp (↑d / 8)⌉₊) := le_trans hge (le_trans hle (Nat.le_ceil _))
  exact_mod_cast h3


/-- For `d ≥ 19`, the size of the Hamming ball of radius `d/4` around `0` multiplied by
`⌈exp(d/8)⌉` is strictly less than `2^d`. -/
lemma _large_d_bound (d : ℕ) (hd : 19 ≤ d) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d).card *
    ⌈Real.exp (↑d / 8)⌉₊ < 2^d := by
  set B := (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d).card
  set M := ⌈Real.exp (↑d / 8)⌉₊
  have htilt : B * 3^(d - d/4) ≤ 4^d := _tilting_real_ball_bound d
  have hnat : 2^d * M < 3^(d - d/4) := _nat_ineq_large d hd
  by_contra h; push Not at h
  have h4d : 4^d = 2^d * 2^d := by rw [show (4:ℕ) = 2*2 from by norm_num, mul_pow]
  have h_BP : B * 3^(d - d/4) ≤ 2^d * 2^d := by linarith
  have h_NP : 2^d * 2^d * M < 2^d * 3^(d-d/4) := by
    have := Nat.mul_lt_mul_of_pos_left hnat (show 0 < 2^d by positivity); linarith
  have h_BMP1 : 2^d * 3^(d-d/4) ≤ B * M * 3^(d-d/4) := Nat.mul_le_mul_right _ h
  have h_BMP2 : B * 3^(d-d/4) * M ≤ 2^d * 2^d * M := Nat.mul_le_mul_right M h_BP
  have h_comm : B * M * 3^(d-d/4) = B * 3^(d-d/4) * M := by ring

  linarith


/-- Decidable reformulation of the radius `(1/2 - 1/4) d` Hamming ball as the integer-arithmetic
filter `4 · |ω| < d`. -/
lemma _ball_filter_decidable (d : ℕ) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d) =
    (Finset.univ.filter fun ω : Fin d → Bool =>
      4 * hammingDist (fun _ => false) ω < d) := by
  ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor
  · intro h; exact_mod_cast (show (4 * hammingDist (fun _ => false) ω : ℝ) < d by nlinarith)
  · intro h
    have h1 : (4 * hammingDist (fun _ => false) ω : ℝ) < (d : ℝ) := by exact_mod_cast h
    linarith


/-- For `d ≤ 8`, `⌈exp(d/8)⌉ ≤ 3`. -/
lemma _ceil_exp_le_3 (d : ℕ) (hd : d ≤ 8) : ⌈Real.exp ((↑d : ℝ) / 8)⌉₊ ≤ 3 := by
  apply Nat.ceil_le.mpr
  have hd8 : (d : ℝ) ≤ 8 := by exact_mod_cast hd
  have h1 : Real.exp ((↑d : ℝ) / 8) ≤ Real.exp 1 := Real.exp_le_exp_of_le (by linarith)
  have h2 : Real.exp (1 : ℝ) < 3 := by linarith [_exp_one_lt]
  linarith


/-- For `d ≤ 18`, `⌈exp(d/8)⌉ ≤ 10`. -/
lemma _ceil_exp_le_10 (d : ℕ) (hd : d ≤ 18) : ⌈Real.exp ((↑d : ℝ) / 8)⌉₊ ≤ 10 := by
  apply Nat.ceil_le.mpr
  have hd18 : (d : ℝ) ≤ 18 := by exact_mod_cast hd
  have h1 : Real.exp ((↑d : ℝ) / 8) ≤ Real.exp ((18:ℝ)/8) := Real.exp_le_exp_of_le (by linarith)

  have h2 : Real.exp ((18:ℝ)/8) < 10 := by
    rw [show (18:ℝ)/8 = 2 + 1/4 from by norm_num, Real.exp_add]
    have he2 : Real.exp (2:ℝ) < 15/2 := by linarith [_exp_two_lt]
    nlinarith [_exp_quarter_lt, Real.exp_pos (2:ℝ), Real.exp_pos ((1:ℝ)/4)]
  linarith


/-- The Hamming distance from the zero vector to `ω` is the number of `true` coordinates. -/
lemma chernoff_hammingDist_false_eq_true_count {d : ℕ} (ω : Fin d → Bool) :
    hammingDist (fun _ => false) ω =
    (Finset.univ.filter fun i : Fin d => ω i = true).card := by
  simp only [hammingDist]; congr 1; ext i; simp [ne_eq]

/-- Per-coordinate tilting product: `∏ (if ω i then 1 else 3) = 3^(d - |ω|)`. -/
lemma chernoff_prod_ite_eq_pow_sub {d : ℕ} (ω : Fin d → Bool) :
    ∏ i : Fin d, (if ω i = true then (1 : ℕ) else 3) =
    3 ^ (d - (Finset.univ.filter fun i : Fin d => ω i = true).card) := by
  rw [Finset.prod_ite (p := fun i => ω i = true)]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1; rw [Finset.filter_not, Finset.card_sdiff]
  simp [Finset.card_univ, Fintype.card_fin]

/-- Tilting identity used in the Chernoff bound: `∑ω 3^(d - |ω|) = 4^d`. -/
lemma chernoff_tilting_identity (d : ℕ) :
    ∑ ω : Fin d → Bool, 3 ^ (d - hammingDist (fun _ => false) ω) = 4 ^ d := by
  simp_rw [chernoff_hammingDist_false_eq_true_count, ← chernoff_prod_ite_eq_pow_sub]
  have h := Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
    (fun (_ : Fin d) (b : Bool) => if b = true then (1 : ℕ) else 3)
  rw [Fintype.piFinset_univ] at h; rw [h]
  conv_lhs => arg 2; ext i; rw [Fintype.sum_bool]
  norm_num

/-- Chernoff/tilting volume bound: `|ball of weight < d/4| · 3^(d - (d-1)/4) ≤ 4^d`. -/
lemma chernoff_tilting_bound (d : ℕ) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      4 * hammingDist (fun _ => false) ω < d).card *
    3 ^ (d - (d - 1) / 4) ≤ 4 ^ d := by
  set ball := Finset.univ.filter fun ω : Fin d → Bool =>
    4 * hammingDist (fun _ => false) ω < d with ball_def
  have step1 : ball.card * 3 ^ (d - (d-1)/4) ≤
      ∑ ω ∈ ball, 3 ^ (d - hammingDist (fun _ => false) ω) := by
    rw [show ball.card * 3 ^ (d-(d-1)/4) = ∑ _ ∈ ball, 3 ^ (d-(d-1)/4) from
      by rw [Finset.sum_const, smul_eq_mul]]
    apply Finset.sum_le_sum; intro ω hω
    apply Nat.pow_le_pow_right (by norm_num : 0 < 3)
    have hmem : 4 * hammingDist (fun _ : Fin d => false) ω < d := by
      rw [ball_def] at hω; exact (Finset.mem_filter.mp hω).2
    omega
  have step2 : ∑ ω ∈ ball, 3 ^ (d - hammingDist (fun _ => false) ω) ≤ 4 ^ d :=
    le_trans (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _))
      (le_of_eq (chernoff_tilting_identity d))
  linarith

/-- The real-valued and integer-valued definitions of the Hamming ball of radius `d/4`
agree as filters. -/
lemma chernoff_filter_eq (d : ℕ) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d) =
    (Finset.univ.filter fun ω : Fin d → Bool =>
      4 * hammingDist (fun _ => false) ω < d) := by
  ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show (1/2 - 1/4 : ℝ) = 1/4 from by norm_num]
  constructor
  · intro h
    have h2 : (4 : ℝ) * ↑(hammingDist (fun _ => false) ω) < ↑d := by linarith
    exact_mod_cast h2
  · intro h
    have h2 : (4 : ℝ) * ↑(hammingDist (fun _ => false) ω) < ↑d := by exact_mod_cast h
    linarith

/-- Numerical bound: `exp(5/8) < 2`. -/
lemma chernoff_exp_five_eighths_lt_two : exp (5/8 : ℝ) < 2 := by
  have h := exp_bound (x := 5/8) (n := 3) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; linarith [h.2]

/-- Numerical bound: `exp(1/2) < 27/16`. -/
lemma chernoff_exp_half_lt : exp (1/2 : ℝ) < 27/16 := by
  have h := exp_bound (x := 1/2) (n := 4) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; linarith [h.2]

/-- Inductive numerical inequality used in the Chernoff bound proof. -/
lemma chernoff_induction_step (x : ℝ) (hx : 0 < x) :
    16 * (x * exp (1/2 : ℝ) + 1) < 27 * (x + 1) := by
  nlinarith [chernoff_exp_half_lt, exp_pos (1/2 : ℝ)]

/-- Base case `d = 6` of `2^d (exp(d/8) + 1) < 3^(d - (d-1)/4)`. -/
lemma chernoff_base6 : (2:ℝ)^6 * (exp (6/8 : ℝ) + 1) < (3:ℝ)^(6 - (6-1)/4) := by
  norm_num; have h := exp_bound (x := 3/4) (n := 5) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; nlinarith [h.2]

/-- Base case `d = 7` of `2^d (exp(d/8) + 1) < 3^(d - (d-1)/4)`. -/
lemma chernoff_base7 : (2:ℝ)^7 * (exp (7/8 : ℝ) + 1) < (3:ℝ)^(7 - (7-1)/4) := by
  norm_num; have h := exp_bound (x := 7/8) (n := 5) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; nlinarith [h.2]

/-- Base case `d = 8` of `2^d (exp(d/8) + 1) < 3^(d - (d-1)/4)`. -/
lemma chernoff_base8 : (2:ℝ)^8 * (exp (8/8 : ℝ) + 1) < (3:ℝ)^(8 - (8-1)/4) := by
  norm_num; have h := exp_bound (x := 1) (n := 5) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; nlinarith [h.2]

/-- Base case `d = 9` of `2^d (exp(d/8) + 1) < 3^(d - (d-1)/4)`. -/
lemma chernoff_base9 : (2:ℝ)^9 * (exp (9/8 : ℝ) + 1) < (3:ℝ)^(9 - (9-1)/4) := by
  norm_num; rw [show (9:ℝ)/8 = 1 + 1/8 from by norm_num, exp_add]
  have h1 := exp_bound (x := 1) (n := 5) (by norm_num) (by norm_num)
  rw [abs_le] at h1; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  have h2 := exp_bound (x := 1/8) (n := 3) (by norm_num) (by norm_num)
  rw [abs_le] at h2; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2
  nlinarith [exp_pos (1 : ℝ), exp_pos (1/8 : ℝ), h1.1, h1.2, h2.1, h2.2]

set_option maxHeartbeats 800000 in
/-- For all `d ≥ 6`, the real inequality `2^d (exp(d/8) + 1) < 3^(d - (d-1)/4)`,
proved by strong induction with step `d ↦ d + 4`. -/
lemma chernoff_real_ineq (d : ℕ) (hd : 6 ≤ d) :
    (2:ℝ)^d * (exp (↑d / 8) + 1) < (3:ℝ)^(d - (d - 1) / 4) := by
  induction d using Nat.strongRecOn with
  | ind n ih =>
  by_cases h10 : n < 10
  · interval_cases n <;>
      first | exact chernoff_base6 | exact chernoff_base7
            | exact chernoff_base8 | exact chernoff_base9
  · push_neg at h10
    have ih_prev := ih (n - 4) (by omega) (by omega)
    rw [show n - (n-1)/4 = ((n-4) - ((n-4)-1)/4) + 3 from by omega,
        pow_add, show (3:ℝ)^3 = 27 from by norm_num]
    rw [show exp (↑n / 8 : ℝ) = exp (↑(n-4) / 8 : ℝ) * exp (1/2 : ℝ) from by
      rw [← exp_add]; congr 1; rw [Nat.cast_sub (by omega : 4 ≤ n)]; ring]
    rw [show (2:ℝ)^n = 16 * (2:ℝ)^(n-4) from by
      rw [show n = (n-4) + 4 from by omega, pow_add]; norm_num; ring]
    nlinarith [ih_prev, chernoff_induction_step (exp (↑(n-4) / 8 : ℝ)) (by positivity),
               (by positivity : (0:ℝ) < (2:ℝ)^(n-4))]

/-- Numerical bound: `2 < exp(3/4)`. -/
lemma chernoff_exp34_gt_two : (2 : ℝ) < exp (3/4 : ℝ) := by
  have h := exp_bound (x := 3/4) (n := 4) (by norm_num) (by norm_num)
  rw [abs_le] at h; simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; linarith [h.1]

/-- For `d ≥ 6`, `max ⌈exp(d/8)⌉ 3 ≤ exp(d/8) + 1`. -/
lemma chernoff_max_bound_large (d : ℕ) (hd : 6 ≤ d) :
    (↑(max (⌈exp (↑d / 8)⌉₊) 3) : ℝ) ≤ exp (↑d / 8) + 1 := by
  rw [Nat.cast_max]
  apply max_le
  · linarith [Nat.ceil_lt_add_one (le_of_lt (exp_pos (↑d / 8)))]
  · linarith [chernoff_exp34_gt_two,
      exp_le_exp_of_le (show (3/4 : ℝ) ≤ ↑d / 8 from by
        linarith [show (6:ℝ) ≤ ↑d from Nat.cast_le.mpr hd])]

set_option maxHeartbeats 800000 in
/-- **Hamming ball volume bound via Chernoff/tilting.** For `d ≥ 2`, the size of the open Hamming
ball of radius `d/4` around `0` multiplied by `max ⌈exp(d/8)⌉ 3` is strictly less than `2^d`. -/
lemma hamming_ball_volume_chernoff_bound (d : ℕ) (hd : 2 ≤ d) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist (fun _ => false) ω : ℝ) < (1/2 - 1/4) * ↑d).card *
    max (⌈Real.exp (↑d / 8)⌉₊) 3 < 2 ^ d := by
  by_cases hd5 : d ≤ 5
  ·
    have hmax : max (⌈exp (↑d / 8)⌉₊) 3 = 3 := by
      have h1 : exp (↑d / 8) < 2 := calc
        exp (↑d / 8) ≤ exp (5/8 : ℝ) := by
          apply exp_le_exp_of_le; linarith [show (d : ℝ) ≤ 5 from Nat.cast_le.mpr hd5]
        _ < 2 := chernoff_exp_five_eighths_lt_two
      exact max_eq_right (show ⌈exp (↑d / 8)⌉₊ ≤ 3 from by
        have : ⌈exp (↑d / 8)⌉₊ ≤ 2 := Nat.ceil_le.mpr (le_of_lt h1); omega)
    rw [hmax, chernoff_filter_eq]
    simp only [hammingDist]
    interval_cases d <;> decide
  ·
    push_neg at hd5
    have hd6 : 6 ≤ d := by omega
    rw [chernoff_filter_eq]
    set c := (Finset.univ.filter fun ω : Fin d → Bool =>
      4 * hammingDist (fun _ => false) ω < d).card
    set M := max (⌈exp (↑d / 8)⌉₊) 3
    have h_tilt := chernoff_tilting_bound d
    have h_real := chernoff_real_ineq d hd6
    have h_max := chernoff_max_bound_large d hd6
    suffices h : (↑(c * M) : ℝ) < ↑(2 ^ d) by exact_mod_cast h
    push_cast
    have hc_nn : (0 : ℝ) ≤ ↑c := Nat.cast_nonneg c
    have h3k_pos : (0 : ℝ) < 3 ^ (d - (d-1)/4) := by positivity
    have h2d_pos : (0 : ℝ) < 2 ^ d := by positivity
    have hexp1_pos : (0 : ℝ) < exp (↑d / 8) + 1 := by positivity
    have h_tilt_r : (↑c : ℝ) * (3:ℝ)^(d-(d-1)/4) ≤ (4:ℝ)^d := by exact_mod_cast h_tilt
    have hc_bound : (↑c : ℝ) ≤ (4:ℝ)^d / (3:ℝ)^(d-(d-1)/4) := by
      rwa [le_div_iff₀ h3k_pos]
    calc (↑c : ℝ) * ↑M
        ≤ ↑c * (exp (↑d / 8) + 1) := mul_le_mul_of_nonneg_left h_max hc_nn
      _ ≤ ((4:ℝ)^d / (3:ℝ)^(d-(d-1)/4)) * (exp (↑d / 8) + 1) :=
          mul_le_mul_of_nonneg_right hc_bound (le_of_lt hexp1_pos)
      _ = (2:ℝ)^d * ((2:ℝ)^d * (exp (↑d / 8) + 1) / (3:ℝ)^(d-(d-1)/4)) := by
          rw [show (4:ℝ)^d = (2:ℝ)^d * (2:ℝ)^d from by rw [← mul_pow]; norm_num]; ring
      _ < (2:ℝ)^d * 1 := by
          apply mul_lt_mul_of_pos_left _ h2d_pos
          rw [div_lt_one h3k_pos]; exact h_real
      _ = (2:ℝ)^d := by ring

/-- Translation-invariant version of the Hamming ball volume bound: for any center `ω₀`, the same
inequality holds. -/
theorem hamming_ball_volume_times_M_lt (d : ℕ) (hd : 2 ≤ d) (ω₀ : Fin d → Bool) :
    (Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d).card *
    max (⌈Real.exp (↑d / 8)⌉₊) 3 < 2 ^ d := by
  rw [hamming_ball_card_eq_zero_center ω₀]
  exact hamming_ball_volume_chernoff_bound d hd

set_option maxHeartbeats 800000 in
/-- The union of Hamming balls of radius `d/4` around at most `max ⌈exp(d/8)⌉ + 1, 4`
already-chosen centers covers strictly fewer than `2^d` vectors, leaving room to greedily
pick a new well-separated vector. -/
theorem hamming_greedy_excluded_bound (d : ℕ) (hd : 2 ≤ d) (S : Finset (Fin d → Bool))
    (hS : S.card + 1 ≤ max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4) :
    (S.biUnion (fun ω₀ =>
      Finset.univ.filter fun ω : Fin d → Bool =>
        (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d)).card < 2 ^ d := by

  set M := max (⌈Real.exp (↑d / 8)⌉₊) 3 with hM_def
  have hS_le : S.card ≤ M := by omega
  have hM_pos : 0 < M := by omega

  set f := fun ω₀ : Fin d → Bool =>
    Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d
  have hball_bound : ∀ ω₀ : Fin d → Bool, (f ω₀).card * M < 2 ^ d :=
    fun ω₀ => hamming_ball_volume_times_M_lt d hd ω₀

  have hd_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
  have hball_le : ∀ ω₀ : Fin d → Bool, (f ω₀).card ≤ (2 ^ d - 1) / M := by
    intro ω₀
    have h := hball_bound ω₀
    rw [Nat.lt_iff_le_pred hd_pos] at h
    exact Nat.le_div_iff_mul_le hM_pos |>.mpr h


  calc (S.biUnion f).card
      ≤ ∑ a ∈ S, (f a).card := Finset.card_biUnion_le
    _ ≤ S.card • ((2 ^ d - 1) / M) := by
        apply Finset.sum_le_card_nsmul
        intro x hx; exact hball_le x
    _ = S.card * ((2 ^ d - 1) / M) := by ring
    _ ≤ M * ((2 ^ d - 1) / M) := Nat.mul_le_mul_right _ hS_le
    _ ≤ 2 ^ d - 1 := Nat.mul_div_le (2 ^ d - 1) M
    _ < 2 ^ d := Nat.sub_lt hd_pos Nat.one_pos

/-- Greedy extension step: given fewer than the threshold many vectors `S`, there exists a new
vector `v` whose Hamming distance to every element of `S` is at least `(1/2 - 1/4) d`. -/
lemma greedy_step (d : ℕ) (hd : 2 ≤ d)
    (S : Finset (Fin d → Bool))
    (hS : S.card + 1 ≤ max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4) :
    ∃ v : Fin d → Bool, ∀ ω₀ ∈ S,
      (hammingDist ω₀ v : ℝ) ≥ (1/2 - 1/4) * ↑d := by
  have hexcl := hamming_greedy_excluded_bound d hd S hS
  have hexcl_lt : (S.biUnion (fun ω₀ =>
    Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d)).card < Fintype.card (Fin d → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact hexcl
  have hne : (S.biUnion (fun ω₀ =>
    Finset.univ.filter fun ω : Fin d → Bool =>
      (hammingDist ω₀ ω : ℝ) < (1/2 - 1/4) * ↑d)) ≠ Finset.univ := by
    intro heq; rw [heq, Finset.card_univ] at hexcl_lt; exact lt_irrefl _ hexcl_lt
  rw [ne_eq, Finset.eq_univ_iff_forall] at hne
  push Not at hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, fun ω₀ hω₀ => ?_⟩
  rw [ge_iff_le, ← not_lt]
  intro hlt
  exact hv (Finset.mem_biUnion.mpr ⟨ω₀, hω₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩)

set_option maxHeartbeats 400000 in
/-- Iterating `greedy_step`: for any `n ≤ max ⌈exp(d/8)⌉ + 1, 4`, one can pick `n` pairwise
`(1/2 - 1/4) d`-separated Boolean vectors. -/
lemma exists_separated_vectors_greedy (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (hn : n ≤ max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4) :
    ∃ (f : Fin n → (Fin d → Bool)),
      ∀ (i j : Fin n), i ≠ j →
        (hammingDist (f i) (f j) : ℝ) ≥ (1/2 - 1/4) * ↑d := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hn' : n ≤ max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4 := by omega
    obtain ⟨f, hf_sep⟩ := ih hn'
    set S := (Finset.univ : Finset (Fin n)).image f
    have hS_card_le : S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    rw [Finset.card_fin] at hS_card_le
    have hS_bound : S.card + 1 ≤ max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4 := by omega
    obtain ⟨v, hv_far⟩ := greedy_step d hd S hS_bound
    refine ⟨fun i => if h : i.val < n then f ⟨i.val, h⟩ else v, ?_⟩
    intro i j hij
    simp only
    split_ifs with hi hj hj
    ·
      exact hf_sep ⟨i, hi⟩ ⟨j, hj⟩
        (by intro heq; apply hij; exact Fin.ext (Fin.mk.inj heq))
    ·
      exact hv_far _ (Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩)
    ·
      rw [hammingDist_symm]
      exact hv_far _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩)
    ·
      exfalso; apply hij; ext; omega

/-- Greedy Varshamov-Gilbert construction: with `M = max ⌈exp(d/8)⌉ + 1, 4`, there exist `M`
pairwise `(1/2 - 1/4) d`-separated Boolean vectors of length `d`. -/
theorem greedy_separated_vectors (d : ℕ) (hd : 2 ≤ d) :
    let M := max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4
    ∃ (ω : Fin M → (Fin d → Bool)),
      ∀ j k : Fin M, j ≠ k →
        (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - 1/4) * ↑d := by
  intro M
  exact exists_separated_vectors_greedy d hd M le_rfl

/-- Strong form of the Varshamov-Gilbert construction: yields `M ≥ exp(d/8) + 1`, `M ≥ 4`, with
pairwise Hamming distance at least `(1/2 - 1/4) d`. -/
theorem vg_strong_construction (d : ℕ) (hd : 2 ≤ d) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    (M : ℝ) ≥ Real.exp (↑d / 8) + 1 ∧
    4 ≤ M ∧
    ∀ j k : Fin M, j ≠ k →
      (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - 1/4) * ↑d := by
  set M := max (⌈Real.exp (↑d / 8)⌉₊ + 1) 4 with hM_def
  obtain ⟨ω, hω⟩ := greedy_separated_vectors d hd
  refine ⟨M, ?_, ω, ?_, ?_, hω⟩
  ·
    exact Nat.lt_of_lt_of_le (by norm_num : 0 < 4) (le_max_right _ _)
  ·
    have h1 : Real.exp (↑d / 8) ≤ ↑(⌈Real.exp (↑d / 8)⌉₊) := Nat.le_ceil _
    have h2 : ⌈Real.exp (↑d / 8)⌉₊ + 1 ≤ M := le_max_left _ _
    calc (M : ℝ) ≥ (↑(⌈Real.exp (↑d / 8)⌉₊ + 1) : ℝ) := by exact_mod_cast h2
      _ = ↑(⌈Real.exp (↑d / 8)⌉₊) + 1 := by push_cast; ring
      _ ≥ Real.exp (↑d / 8) + 1 := by linarith
  ·
    exact le_max_right _ _

/-- Specialization of Varshamov-Gilbert used in Corollary 5.13: provides `M ≥ exp((1/4)² d / 2)`,
`M ≥ 4`, `log(M - 1) ≥ d/8`, and `(1/2 - 1/4) d`-pairwise-separated vectors. -/
lemma varshamov_gilbert_for_cor513 (d : ℕ) (hd : 2 ≤ d) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    (M : ℝ) ≥ Real.exp ((1/4 : ℝ) ^ 2 * ↑d / 2) ∧
    4 ≤ M ∧
    Real.log ((M : ℝ) - 1) ≥ ↑d / 8 ∧
    ∀ j k : Fin M, j ≠ k →
      (hammingDist (ω j) (ω k) : ℝ) ≥ (1/2 - 1/4) * ↑d := by
  obtain ⟨M, hM_pos, ω, hM_large, hM4, hω_sep⟩ := vg_strong_construction d hd
  refine ⟨M, hM_pos, ω, ?_, hM4, ?_, hω_sep⟩
  ·

    calc (M : ℝ) ≥ Real.exp (↑d / 8) + 1 := hM_large
      _ ≥ Real.exp (↑d / 8) := le_add_of_nonneg_right zero_le_one
      _ ≥ Real.exp ((1/4 : ℝ) ^ 2 * ↑d / 2) := by
          apply Real.exp_le_exp.mpr
          have hd_nn : (0 : ℝ) ≤ ↑d := Nat.cast_nonneg d
          nlinarith
  ·


    have hM_real : (M : ℝ) ≥ Real.exp (↑d / 8) + 1 := hM_large
    have hexp_pos : (0 : ℝ) < Real.exp (↑d / 8) := Real.exp_pos _
    have hM_sub : (M : ℝ) - 1 ≥ Real.exp (↑d / 8) := by linarith
    calc Real.log ((M : ℝ) - 1)
        ≥ Real.log (Real.exp (↑d / 8)) :=
          Real.log_le_log hexp_pos hM_sub
      _ = ↑d / 8 := Real.log_exp _

end InfoTheory

end
