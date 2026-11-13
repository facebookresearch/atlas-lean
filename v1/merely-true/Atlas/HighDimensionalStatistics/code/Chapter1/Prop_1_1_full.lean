/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Prop_1_1
import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 800000

open MeasureTheory Set Real Filter Topology ProbabilityTheory ENNReal

namespace Rigollet.Chapter1

/-- Closed form of the standard-normal density:
`φ(x) = (2π)^{-1/2} · exp(-x²/2)`. -/
lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * rexp (-(x ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, sq]
  ring_nf

/-- Symmetry of the standard Gaussian: `P(X < -t) = P(X > t)`. -/
lemma gaussianReal_Iio_neg_eq_Ioi (t : ℝ) :
    gaussianReal 0 1 (Iio (-t)) = gaussianReal 0 1 (Ioi t) := by
  have hmap := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  simp only [neg_zero] at hmap
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi t) = Iio (-t) := by ext x; simp
  conv_lhs => rw [← hpre]
  rw [← Measure.map_apply (by fun_prop) measurableSet_Ioi, hmap]

/-- **Proposition 1.1 (Gaussian upper-tail bound, standard normal).**
For `t > 0`, the standard normal satisfies
`P(X > t) ≤ (2π)^{-1/2} · t⁻¹ · exp(-t²/2)`. -/
theorem proposition_1_1_mills_prob_upper (t : ℝ) (ht : 0 < t) :
    gaussianReal 0 1 (Ioi t) ≤
      ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  apply ENNReal.ofReal_le_ofReal
  have h_eq : ∫ x in Ioi t, gaussianPDFReal 0 1 x =
      (√(2 * π))⁻¹ * ∫ x in Ioi t, rexp (-(x ^ 2 / 2)) := by
    have hf : (fun x => gaussianPDFReal 0 1 x) =
        (fun x => (√(2 * π))⁻¹ * rexp (-(x ^ 2 / 2))) := by
      funext x; exact gaussianPDFReal_zero_one x
    rw [hf, integral_const_mul]
  rw [h_eq]
  calc (√(2 * π))⁻¹ * ∫ x in Ioi t, rexp (-(x ^ 2 / 2))
      ≤ (√(2 * π))⁻¹ * (t⁻¹ * rexp (-(t ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left (proposition_1_1_mills_inequality t ht) (by positivity)
    _ = (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2)) := by ring

/-- Symmetric lower-tail version of Proposition 1.1 for the standard normal:
`P(X < -t) ≤ (2π)^{-1/2} · t⁻¹ · exp(-t²/2)`. -/
theorem proposition_1_1_mills_prob_lower (t : ℝ) (ht : 0 < t) :
    gaussianReal 0 1 (Iio (-t)) ≤
      ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) := by
  rw [gaussianReal_Iio_neg_eq_Ioi]
  exact proposition_1_1_mills_prob_upper t ht

/-- Two-sided version of Proposition 1.1 for the standard normal:
`P(|X| > t) ≤ 2 · (2π)^{-1/2} · t⁻¹ · exp(-t²/2)`. -/
theorem proposition_1_1_mills_prob_abs (t : ℝ) (ht : 0 < t) :
    gaussianReal 0 1 {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (2 * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) := by
  have hset : {x : ℝ | t < |x|} = Ioi t ∪ Iio (-t) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio]
    constructor
    · intro h
      by_cases hx : 0 ≤ x
      · left; rwa [abs_of_nonneg hx] at h
      · push Not at hx; right; rw [abs_of_neg hx] at h; linarith
    · rintro (h | h)
      · exact lt_of_lt_of_le h (le_abs_self x)
      · have : -x ≤ |x| := neg_le_abs x; linarith
  rw [hset]
  have hdisj : Disjoint (Ioi t) (Iio (-t)) := by
    rw [Set.disjoint_iff]; intro x ⟨h1, h2⟩
    simp only [mem_Ioi, mem_Iio] at h1 h2; linarith
  rw [measure_union hdisj measurableSet_Iio]
  rw [gaussianReal_Iio_neg_eq_Ioi]
  have hupper := proposition_1_1_mills_prob_upper t ht
  have hnn : 0 ≤ (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2)) := by positivity
  calc gaussianReal 0 1 (Ioi t) + gaussianReal 0 1 (Ioi t)
      ≤ ENNReal.ofReal ((√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) +
        ENNReal.ofReal ((√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) :=
        add_le_add hupper hupper
    _ = ENNReal.ofReal (2 * ((√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2)))) := by
        rw [← ENNReal.ofReal_add hnn hnn]; congr 1; ring
    _ = ENNReal.ofReal (2 * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / 2))) := by
        congr 1; ring

/-- Translation invariance: the probability `P(X > m + s)` for `X ~ N(m, v)`
equals `P(X > s)` for the centered Gaussian `N(0, v)`. -/
lemma gaussianReal_shift_Ioi (m : ℝ) (v : NNReal) (s : ℝ) :
    gaussianReal m v (Ioi (m + s)) = gaussianReal 0 v (Ioi s) := by
  have hmap := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := v) m
  simp only [zero_add] at hmap
  rw [← hmap, Measure.map_apply (measurable_add_const m) measurableSet_Ioi]
  congr 1; ext x; simp only [mem_preimage, mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Lower-tail translation invariance for Gaussians:
`P(X < m + s) = P(X' < s)` where `X ~ N(m,v)` and `X' ~ N(0,v)`. -/
lemma gaussianReal_shift_Iio (m : ℝ) (v : NNReal) (s : ℝ) :
    gaussianReal m v (Iio (m + s)) = gaussianReal 0 v (Iio s) := by
  have hmap := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := v) m
  simp only [zero_add] at hmap
  rw [← hmap, Measure.map_apply (measurable_add_const m) measurableSet_Iio]
  congr 1; ext x; simp only [mem_preimage, mem_Iio]
  constructor <;> intro h <;> linarith

/-- Scaling identity: for the centered Gaussian with variance `σ²`,
`P(X > t) = P(X' > t/σ)` where `X' ~ N(0,1)`. -/
lemma gaussianReal_zero_scale_Ioi_div (σ t : ℝ) (hσ : 0 < σ) :
    gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ (Ioi t) = gaussianReal 0 1 (Ioi (t / σ)) := by
  have hmap : (gaussianReal 0 1).map (σ * ·) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ := by
    have := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) σ
    simp only [mul_zero, mul_one] at this
    exact this
  rw [← hmap, Measure.map_apply (measurable_const_mul σ) measurableSet_Ioi]
  congr 1; ext x; simp only [mem_preimage, mem_Ioi]
  rw [div_lt_iff₀ hσ, mul_comm]

/-- Symmetry of any centered Gaussian: `P(X < -s) = P(X > s)`. -/
lemma gaussianReal_zero_Iio_neg (v : NNReal) (s : ℝ) :
    gaussianReal 0 v (Iio (-s)) = gaussianReal 0 v (Ioi s) := by
  have hmap_neg := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
  simp only [neg_zero] at hmap_neg
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi s) = Iio (-s) := by ext x; simp
  conv_lhs => rw [← hpre]
  rw [← Measure.map_apply (by fun_prop) measurableSet_Ioi, hmap_neg]

/-- **Proposition 1.1 (general Gaussian upper tail).** For `X ~ N(m, σ²)`
with `σ > 0` and `t > 0`,
`P(X > m + t) ≤ σ · (2π)^{-1/2} · t⁻¹ · exp(-t²/(2σ²))`. -/
theorem proposition_1_1_mills_prob_upper_general (m : ℝ) (σ : ℝ) (hσ : 0 < σ)
    (t : ℝ) (ht : 0 < t) :
    gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ (Ioi (m + t)) ≤
      ENNReal.ofReal (σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) := by
  rw [gaussianReal_shift_Ioi, gaussianReal_zero_scale_Ioi_div σ t hσ]
  have htσ : 0 < t / σ := div_pos ht hσ
  have h := proposition_1_1_mills_prob_upper (t / σ) htσ
  convert h using 2
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp [hσ', ht']

/-- General Gaussian lower-tail bound (Proposition 1.1): for `X ~ N(m, σ²)`,
`P(X < m - t) ≤ σ · (2π)^{-1/2} · t⁻¹ · exp(-t²/(2σ²))`. -/
theorem proposition_1_1_mills_prob_lower_general (m : ℝ) (σ : ℝ) (hσ : 0 < σ)
    (t : ℝ) (ht : 0 < t) :
    gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ (Iio (m - t)) ≤
      ENNReal.ofReal (σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) := by
  have hshift : m - t = m + (-t) := by ring
  rw [hshift, gaussianReal_shift_Iio]
  rw [gaussianReal_zero_Iio_neg]
  rw [gaussianReal_zero_scale_Ioi_div σ t hσ]
  have htσ : 0 < t / σ := div_pos ht hσ
  have h := proposition_1_1_mills_prob_upper (t / σ) htσ
  convert h using 2
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp [hσ', ht']

/-- General two-sided Gaussian tail (Proposition 1.1): for `X ~ N(m, σ²)`,
`P(|X - m| > t) ≤ 2σ · (2π)^{-1/2} · t⁻¹ · exp(-t²/(2σ²))`. -/
theorem proposition_1_1_mills_prob_abs_general (m : ℝ) (σ : ℝ) (hσ : 0 < σ)
    (t : ℝ) (ht : 0 < t) :
    gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ {x : ℝ | t < |x - m|} ≤
      ENNReal.ofReal (2 * σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) := by
  have hset : {x : ℝ | t < |x - m|} = Ioi (m + t) ∪ Iio (m - t) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioi, mem_Iio]
    constructor
    · intro h
      by_cases hx : 0 ≤ x - m
      · left; rw [abs_of_nonneg hx] at h; linarith
      · push Not at hx; right; rw [abs_of_neg hx] at h; linarith
    · rintro (h | h)
      · have : x - m > t := by linarith
        exact lt_of_lt_of_le this (le_abs_self (x - m))
      · have : -(x - m) > t := by linarith
        calc t < -(x - m) := this
          _ ≤ |x - m| := neg_le_abs (x - m)
  rw [hset]
  have hdisj : Disjoint (Ioi (m + t)) (Iio (m - t)) := by
    rw [Set.disjoint_iff]; intro x ⟨h1, h2⟩
    simp only [mem_Ioi, mem_Iio] at h1 h2; linarith
  rw [measure_union hdisj measurableSet_Iio]
  have hupper := proposition_1_1_mills_prob_upper_general m σ hσ t ht
  have hlower := proposition_1_1_mills_prob_lower_general m σ hσ t ht
  have hnn : 0 ≤ σ * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2))) := by positivity
  calc gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ (Ioi (m + t)) +
        gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ (Iio (m - t))
      ≤ ENNReal.ofReal (σ * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) +
        ENNReal.ofReal (σ * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) :=
        add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * (σ * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2))))) := by
        rw [← ENNReal.ofReal_add hnn hnn]; congr 1; ring
    _ = ENNReal.ofReal (2 * σ * (√(2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) := by
        congr 1; ring

end Rigollet.Chapter1

namespace GaussianTailBound

open Rigollet.Chapter1

/-- Public packaging of Proposition 1.1: upper, lower and two-sided
Mills-type tail bounds for any Gaussian `N(μ, σ²)`. -/
theorem gaussian_tail_bound (μ : ℝ) (σ : ℝ) (hσ : σ > 0) (t : ℝ) (ht : t > 0) :
    gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩ (Ioi (μ + t)) ≤
      ENNReal.ofReal (σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) ∧
    gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩ (Iio (μ - t)) ≤
      ENNReal.ofReal (σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) ∧
    gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩ {x : ℝ | t < |x - μ|} ≤
      ENNReal.ofReal (2 * σ * (Real.sqrt (2 * π))⁻¹ * t⁻¹ * rexp (-(t ^ 2 / (2 * σ ^ 2)))) :=
  ⟨proposition_1_1_mills_prob_upper_general μ σ hσ t ht,
   proposition_1_1_mills_prob_lower_general μ σ hσ t ht,
   proposition_1_1_mills_prob_abs_general μ σ hσ t ht⟩

end GaussianTailBound
