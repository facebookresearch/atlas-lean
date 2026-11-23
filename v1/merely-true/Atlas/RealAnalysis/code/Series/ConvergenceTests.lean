/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter Topology

namespace Real_Analysis.Series

/-- **Comparison Test for series of real numbers.**
If `0 ≤ x n ≤ y n` for every `n`, then:
1. summability of `y` implies summability of `x`, and
2. non-summability of `x` implies non-summability of `y`
(the latter being the contrapositive of the former). -/
theorem comparison_test (x y : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (hxy : ∀ n, x n ≤ y n) :
    (Summable y → Summable x) ∧ (¬ Summable x → ¬ Summable y) := by
  have h1 : Summable y → Summable x :=
    fun hy => Summable.of_nonneg_of_le hx hxy hy
  exact ⟨h1, fun hns hy => hns (h1 hy)⟩

/-- **Root Test (Cauchy's root test).**
Suppose `L = lim |x n| ^ (1/n)` exists. Then:
1. if `L < 1`, the series `∑ |x n|` converges (so `∑ x n` converges absolutely);
2. if `L > 1`, the series `∑ x n` diverges. -/
theorem root_test (x : ℕ → ℝ) (L : ℝ)
    (hL : Tendsto (fun n => |x n| ^ ((1 : ℝ) / n)) atTop (nhds L)) :
    (L < 1 → Summable (fun n => |x n|)) ∧ (1 < L → ¬ Summable x) := by
  constructor
  ·
    intro hL1

    obtain ⟨r, hLr, hr1⟩ := exists_between hL1
    have hr0 : 0 ≤ r := by
      have : 0 ≤ L := by
        apply ge_of_tendsto hL
        apply eventually_atTop.mpr
        exact ⟨1, fun n _ => Real.rpow_nonneg (abs_nonneg _) _⟩
      linarith

    have hev : ∀ᶠ n in atTop, |x n| ^ ((1 : ℝ) / ↑n) < r := hL (Iio_mem_nhds hLr)

    apply Summable.of_norm_bounded_eventually_nat (g := fun n => r ^ n)
      (summable_geometric_of_lt_one hr0 hr1)

    have hev1 : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    apply (hev.and hev1).mono
    intro n ⟨hn_lt, hn_pos⟩
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have hn_ne : (n : ℕ) ≠ 0 := by omega

    have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
    rw [h_eq] at hn_lt
    have h1 : (|x n| ^ ((↑n : ℝ)⁻¹)) ^ n ≤ r ^ n := by
      apply pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) _)
      exact le_of_lt hn_lt
    rwa [Real.rpow_inv_natCast_pow (abs_nonneg _) hn_ne] at h1
  ·
    intro hL1

    have hev : ∀ᶠ n in atTop, 1 < |x n| ^ ((1 : ℝ) / ↑n) := hL (Ioi_mem_nhds hL1)

    have hev1 : ∀ᶠ n in atTop, 1 < |x n| := by
      have hev_pos : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
      apply (hev.and hev_pos).mono
      intro n ⟨hn_gt, hn_pos⟩
      have hn_ne : (n : ℕ) ≠ 0 := by omega
      have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
      rw [h_eq] at hn_gt
      have h1 : (1 : ℝ) ^ n < (|x n| ^ ((↑n : ℝ)⁻¹)) ^ n := by
        apply pow_lt_pow_left₀ hn_gt (le_of_lt zero_lt_one) hn_ne
      rw [one_pow, Real.rpow_inv_natCast_pow (abs_nonneg _) hn_ne] at h1
      exact h1

    intro hsum
    have h0 := hsum.tendsto_atTop_zero
    have h_abs0 : Tendsto (fun n => |x n|) atTop (nhds 0) := by
      rw [← abs_zero]; exact Tendsto.abs h0
    have h2 : ∀ᶠ n in atTop, |x n| < 1 := h_abs0 (Iio_mem_nhds one_pos)
    have h3 := h2.and hev1
    obtain ⟨n, hn1, hn2⟩ := h3.exists
    linarith

/-- **Ratio Test (d'Alembert's ratio test).**
Suppose `x n ≠ 0` for every `n` and `L = lim |x (n+1)| / |x n|` exists. Then:
1. if `L < 1`, the series `∑ |x n|` converges (so `∑ x n` converges absolutely);
2. if `L > 1`, the series `∑ x n` diverges. -/
theorem ratio_test (x : ℕ → ℝ) (L : ℝ) (hx : ∀ n, x n ≠ 0)
    (hL : Filter.Tendsto (fun n => |x (n+1)| / |x n|) Filter.atTop (nhds L)) :
    (L < 1 → Summable (fun n => |x n|)) ∧ (1 < L → ¬ Summable x) := by
  constructor
  · intro hL1
    have hne : ∀ᶠ n in atTop, (fun n => |x n|) n ≠ 0 :=
      Filter.Eventually.of_forall (fun n => by simp [hx n])
    have htend : Tendsto (fun n => ‖(fun m => |x m|) (n + 1)‖ / ‖(fun m => |x m|) n‖) atTop (𝓝 L) := by
      simp only [Real.norm_eq_abs, abs_abs]
      exact hL
    exact summable_of_ratio_test_tendsto_lt_one hL1 hne htend
  · intro hL1
    have htend : Tendsto (fun n => ‖x (n + 1)‖ / ‖x n‖) atTop (𝓝 L) := by
      simp only [Real.norm_eq_abs]
      exact hL
    exact not_summable_of_ratio_test_tendsto_gt_one hL1 htend

/-- **Alternating Series Test (Leibniz's test).**
If `x : ℕ → ℝ` is nonnegative, monotone decreasing (`Antitone`), and tends to `0`,
then the alternating series `∑ (-1)^i * x i` converges, i.e. its partial sums
converge to some real limit `l`. -/
theorem alternating_series_test (x : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ x n)
    (hdec : Antitone x)
    (hlim : Filter.Tendsto x Filter.atTop (nhds 0)) :
    ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * x i)
      Filter.atTop (nhds l) := by
  have _ := hpos
  exact hdec.tendsto_alternating_series_of_tendsto_zero hlim

/-- **Convergence of the alternating harmonic series.**
The series `∑ (-1)^i / (i + 1)` converges, i.e. its partial sums converge to some
real limit `l`. This is a direct corollary of the alternating series test, applied
to the decreasing positive sequence `1 / (n + 1)`. Note that the corresponding
series of absolute values (the harmonic series) diverges, so this is an example
of a conditionally convergent series. -/
theorem alternating_harmonic_converges :
    ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i / (↑i + 1)))
      Filter.atTop (nhds l) := by
  have heq : (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i / (↑i + 1))) =
    (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i * (1 / (↑i + 1)))) := by
    ext n; congr 1; ext i; ring
  rw [heq]
  have hdec : Antitone (fun n : ℕ => (1 : ℝ) / (↑n + 1)) := by
    intro a b hab
    apply div_le_div_of_nonneg_left
    · exact zero_lt_one.le
    · positivity
    · linarith [show (↑a : ℝ) ≤ ↑b from Nat.cast_le.mpr hab]
  have hlim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => (↑n + 1 : ℝ)⁻¹) Filter.atTop (nhds 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simp only [div_eq_mul_inv, one_mul] at this ⊢
    exact this
  exact hdec.tendsto_alternating_series_of_tendsto_zero hlim

end Real_Analysis.Series
