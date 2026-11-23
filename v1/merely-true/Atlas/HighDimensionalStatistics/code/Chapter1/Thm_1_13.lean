/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11

open MeasureTheory ProbabilityTheory Real Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Bernstein's inequality, right tail.** For independent `X_i` whose MGFs
satisfy a sub-exponential bound `mgf(X_i)(s) ≤ exp(s² λ²/2)` on
`|s| ≤ 1/λ`, the centered sample mean satisfies
`P(X̄ ≥ t) ≤ exp(-(n/2) min(t²/λ², t/λ))`. -/
theorem bernstein_right_tail
    {n : ℕ} {X : Fin n → Ω → ℝ} {t lambda : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hlam : 0 < lambda)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_mgf : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      mgf (X i) μ s ≤ exp (s ^ 2 * lambda ^ 2 / 2))
    (h_int : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      Integrable (fun ω => exp (s * X i ω)) μ) :
    μ.real {ω | t ≤ (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω} ≤
      exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) := by
  set s₀ := min (1 / lambda) (t / lambda ^ 2) with hs₀_def
  have hs₀_pos : 0 < s₀ := lt_min (by positivity) (by positivity)
  have hs₀_bound : |s₀| ≤ 1 / lambda := by
    rw [abs_of_pos hs₀_pos]; exact min_le_left _ _

  have h_set_eq : {ω | t ≤ (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω} =
      {ω | ↑n * t ≤ ∑ i : Fin n, X i ω} := by
    ext ω; simp only [Set.mem_setOf_eq]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < ↑n)]
    ring_nf
  rw [h_set_eq]

  have h_int_sum : Integrable (fun ω => exp (s₀ * ∑ i : Fin n, X i ω)) μ := by
    have : (fun ω => exp (s₀ * ∑ i : Fin n, X i ω)) =
        (fun ω => exp (s₀ * (∑ i ∈ Finset.univ, X i) ω)) := by
      ext ω; congr 1; congr 1; simp [Finset.sum_apply]
    rw [this]
    exact h_indep.integrable_exp_mul_sum h_meas (fun i _ => h_int i s₀ hs₀_bound)

  have step1 := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i : Fin n, X i ω)
    (μ := μ) (t := s₀) (↑n * t) (le_of_lt hs₀_pos) h_int_sum

  have h_factor : mgf (fun ω => ∑ i : Fin n, X i ω) μ s₀ =
      ∏ i : Fin n, mgf (X i) μ s₀ := by
    have : mgf (fun ω => ∑ i : Fin n, X i ω) μ s₀ =
        mgf (∑ i ∈ Finset.univ, X i) μ s₀ := by
      congr 1; ext ω; simp [Finset.sum_apply]
    rw [this, h_indep.mgf_sum h_meas]

  have h_prod : ∏ i : Fin n, mgf (X i) μ s₀ ≤ exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) := by
    calc ∏ i : Fin n, mgf (X i) μ s₀
        ≤ ∏ _i : Fin n, exp (s₀ ^ 2 * lambda ^ 2 / 2) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => h_mgf i s₀ hs₀_bound)
      _ = exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) := by
          rw [Finset.prod_const, Finset.card_fin, exp_nat_mul]

  have step3 : ↑n * (s₀ ^ 2 * lambda ^ 2 / 2 - s₀ * t) ≤
      -(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda)) := by
    by_cases h : t ≤ lambda
    · have hle : t / lambda ^ 2 ≤ 1 / lambda := by
        rw [div_le_div_iff₀ (by positivity) hlam]
        nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt ht)]
      have hle2 : t ^ 2 / lambda ^ 2 ≤ t / lambda := by
        rw [div_le_div_iff₀ (by positivity) hlam]
        nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos ht hlam))]
      rw [hs₀_def, min_eq_right hle, min_eq_left hle2]
      have key : (t / lambda ^ 2) ^ 2 * lambda ^ 2 / 2 - t / lambda ^ 2 * t =
          -(t ^ 2 / lambda ^ 2 / 2) := by field_simp; ring
      rw [key]; nlinarith
    · push_neg at h
      have hle : 1 / lambda ≤ t / lambda ^ 2 := by
        rw [div_le_div_iff₀ hlam (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt hlam)]
      have hle2 : t / lambda ≤ t ^ 2 / lambda ^ 2 := by
        rw [div_le_div_iff₀ hlam (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt (mul_pos ht hlam))]
      rw [hs₀_def, min_eq_left hle, min_eq_right hle2]
      have key : (1 / lambda) ^ 2 * lambda ^ 2 / 2 - 1 / lambda * t =
          1 / 2 - t / lambda := by field_simp
      rw [key]
      have ht_ge : 1 ≤ t / lambda := by rw [le_div_iff₀ hlam]; linarith
      nlinarith

  calc μ.real {ω | ↑n * t ≤ ∑ i : Fin n, X i ω}
      ≤ exp (-s₀ * (↑n * t)) * mgf (fun ω => ∑ i : Fin n, X i ω) μ s₀ := step1
    _ = exp (-s₀ * (↑n * t)) * ∏ i : Fin n, mgf (X i) μ s₀ := by rw [h_factor]
    _ ≤ exp (-s₀ * (↑n * t)) * exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left h_prod (exp_pos _).le
    _ = exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2 - s₀ * t)) := by
        rw [← exp_add]; ring_nf
    _ ≤ exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) :=
        exp_le_exp.mpr step3

/-- **Bernstein's inequality, left tail.** Symmetric lower-tail counterpart
of `bernstein_right_tail`:
`P(X̄ ≤ -t) ≤ exp(-(n/2) min(t²/λ², t/λ))`. -/
theorem bernstein_left_tail
    {n : ℕ} {X : Fin n → Ω → ℝ} {t lambda : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hlam : 0 < lambda)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_mgf : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      mgf (X i) μ s ≤ exp (s ^ 2 * lambda ^ 2 / 2))
    (h_int : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      Integrable (fun ω => exp (s * X i ω)) μ) :
    μ.real {ω | (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω ≤ -t} ≤
      exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) := by
  set s₀ := min (1 / lambda) (t / lambda ^ 2) with hs₀_def
  have hs₀_pos : 0 < s₀ := lt_min (by positivity) (by positivity)
  have hs₀_bound : |s₀| ≤ 1 / lambda := by
    rw [abs_of_pos hs₀_pos]; exact min_le_left _ _
  have hns₀_bound : |-s₀| ≤ 1 / lambda := by rw [abs_neg]; exact hs₀_bound

  have h_set_eq : {ω | (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω ≤ -t} =
      {ω | (fun ω => ∑ i : Fin n, X i ω) ω ≤ -(↑n * t)} := by
    ext ω; simp only [Set.mem_setOf_eq]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ↑n)]
    ring_nf
  rw [h_set_eq]

  have h_int_sum : Integrable (fun ω => exp (-s₀ * ∑ i : Fin n, X i ω)) μ := by
    have : (fun ω => exp (-s₀ * ∑ i : Fin n, X i ω)) =
        (fun ω => exp (-s₀ * (∑ i ∈ Finset.univ, X i) ω)) := by
      ext ω; congr 1; congr 1; simp [Finset.sum_apply]
    rw [this]
    exact h_indep.integrable_exp_mul_sum h_meas (fun i _ => h_int i (-s₀) hns₀_bound)

  have step1 := measure_le_le_exp_mul_mgf (X := fun ω => ∑ i : Fin n, X i ω)
    (μ := μ) (t := -s₀) (-(↑n * t)) (neg_nonpos.mpr (le_of_lt hs₀_pos)) h_int_sum

  have h_factor : mgf (fun ω => ∑ i : Fin n, X i ω) μ (-s₀) =
      ∏ i : Fin n, mgf (X i) μ (-s₀) := by
    have : mgf (fun ω => ∑ i : Fin n, X i ω) μ (-s₀) =
        mgf (∑ i ∈ Finset.univ, X i) μ (-s₀) := by
      congr 1; ext ω; simp [Finset.sum_apply]
    rw [this, h_indep.mgf_sum h_meas]

  have h_prod : ∏ i : Fin n, mgf (X i) μ (-s₀) ≤ exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) := by
    calc ∏ i : Fin n, mgf (X i) μ (-s₀)
        ≤ ∏ _i : Fin n, exp ((-s₀) ^ 2 * lambda ^ 2 / 2) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => h_mgf i (-s₀) hns₀_bound)
      _ = exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) := by
          rw [neg_sq]; rw [Finset.prod_const, Finset.card_fin, exp_nat_mul]

  have step3 : ↑n * (s₀ ^ 2 * lambda ^ 2 / 2 - s₀ * t) ≤
      -(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda)) := by
    by_cases h : t ≤ lambda
    · have hle : t / lambda ^ 2 ≤ 1 / lambda := by
        rw [div_le_div_iff₀ (by positivity) hlam]
        nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt ht)]
      have hle2 : t ^ 2 / lambda ^ 2 ≤ t / lambda := by
        rw [div_le_div_iff₀ (by positivity) hlam]
        nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos ht hlam))]
      rw [hs₀_def, min_eq_right hle, min_eq_left hle2]
      have key : (t / lambda ^ 2) ^ 2 * lambda ^ 2 / 2 - t / lambda ^ 2 * t =
          -(t ^ 2 / lambda ^ 2 / 2) := by field_simp; ring
      rw [key]; nlinarith
    · push_neg at h
      have hle : 1 / lambda ≤ t / lambda ^ 2 := by
        rw [div_le_div_iff₀ hlam (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt hlam)]
      have hle2 : t / lambda ≤ t ^ 2 / lambda ^ 2 := by
        rw [div_le_div_iff₀ hlam (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h) (le_of_lt (mul_pos ht hlam))]
      rw [hs₀_def, min_eq_left hle, min_eq_right hle2]
      have key : (1 / lambda) ^ 2 * lambda ^ 2 / 2 - 1 / lambda * t =
          1 / 2 - t / lambda := by field_simp
      rw [key]
      have ht_ge : 1 ≤ t / lambda := by rw [le_div_iff₀ hlam]; linarith
      nlinarith

  calc μ.real {ω | (fun ω => ∑ i : Fin n, X i ω) ω ≤ -(↑n * t)}
      ≤ exp (- -s₀ * (-(↑n * t))) * mgf (fun ω => ∑ i : Fin n, X i ω) μ (-s₀) := step1
    _ = exp (-s₀ * (↑n * t)) * mgf (fun ω => ∑ i : Fin n, X i ω) μ (-s₀) := by ring_nf
    _ = exp (-s₀ * (↑n * t)) * ∏ i : Fin n, mgf (X i) μ (-s₀) := by rw [h_factor]
    _ ≤ exp (-s₀ * (↑n * t)) * exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left h_prod (exp_pos _).le
    _ = exp (↑n * (s₀ ^ 2 * lambda ^ 2 / 2 - s₀ * t)) := by
        rw [← exp_add]; ring_nf
    _ ≤ exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) :=
        exp_le_exp.mpr step3

/-- **Theorem 1.13 (Bernstein's inequality).** For independent
sub-exponential variables `X₁,…,Xₙ` with parameter `λ`, the maximum of the
two centered sample-mean tail probabilities is bounded by
`exp(-(n/2) min(t²/λ², t/λ))`. -/
theorem theorem_1_13_bernstein_inequality
    {n : ℕ} {X : Fin n → Ω → ℝ} {t lambda : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hlam : 0 < lambda)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sub_exp : ∀ i, IsSubExponential (μ := μ) (X i) lambda)
    (h_int : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      Integrable (fun ω => exp (s * X i ω)) μ) :
    max (μ.real {ω | t ≤ (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω})
        (μ.real {ω | (1 / ↑n : ℝ) * ∑ i : Fin n, X i ω ≤ -t}) ≤
      exp (-(↑n / 2 * min (t ^ 2 / lambda ^ 2) (t / lambda))) := by
  have h_mgf : ∀ i, ∀ s : ℝ, |s| ≤ 1 / lambda →
      mgf (X i) μ s ≤ exp (s ^ 2 * lambda ^ 2 / 2) := by
    intro i s hs
    exact (h_sub_exp i).2.2.2 s hs
  exact max_le
    (bernstein_right_tail hn ht hlam h_indep h_meas h_mgf h_int)
    (bernstein_left_tail hn ht hlam h_indep h_meas h_mgf h_int)
