/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Mathlib

open Finset Matrix BigOperators Rigollet MeasureTheory

namespace Rigollet

/-- Deterministic slow-rate bound for the Lasso: if `|Xᵀε|_∞ ≤ n τ` then
`‖X(θ̂ - θ*)‖² ≤ 4 n τ ‖θ*‖₁`. This is the key deterministic input to Theorem 2.15. -/
theorem theorem_2_15_lasso_slow_rate
    {n d : ℕ} (hn : 0 < (n : ℝ))
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hY : IsLassoEstimatorL2 X (X.mulVec θstar + ε) τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i : Fin n, X i j * ε i| ≤ ↑n * τ) :
    sqL2norm (X.mulVec (θhat - θstar)) ≤ 4 * ↑n * τ * l1norm θstar := by

  have h1 := hY.2 θstar

  have hres : (X.mulVec θstar + ε) - X.mulVec θhat = ε - X.mulVec (θhat - θstar) := by
    simp [Matrix.mulVec_sub]; ext i; simp [Pi.sub_apply, Pi.add_apply]; ring
  have hres_star : (X.mulVec θstar + ε) - X.mulVec θstar = ε := by
    ext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [hres, hres_star] at h1

  set δ := X.mulVec (θhat - θstar) with hδ_def

  have hexpand : sqL2norm (ε - δ) = sqL2norm ε - 2 * ∑ i, ε i * δ i + sqL2norm δ := by
    simp only [sqL2norm, Pi.sub_apply]
    simp_rw [fun i : Fin n => show (ε i - δ i) ^ 2 = ε i ^ 2 - 2 * (ε i * δ i) + δ i ^ 2 from by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand] at h1

  set A := sqL2norm ε
  set B := ∑ i, ε i * δ i
  set C := sqL2norm δ
  set D := 2 * τ * l1norm θhat
  set E := 2 * τ * l1norm θstar
  have h2 : C ≤ 2 * B + ↑n * (E - D) := by
    have key : 1 / ↑n * C ≤ 1 / ↑n * (2 * B) + (E - D) := by
      linarith [show 1 / (↑n : ℝ) * (A - 2 * B + C) =
        1 / ↑n * A - 1 / ↑n * (2 * B) + 1 / ↑n * C from by ring]
    calc C = ↑n * (1 / ↑n * C) := by field_simp
      _ ≤ ↑n * (1 / ↑n * (2 * B) + (E - D)) := by
          apply mul_le_mul_of_nonneg_left key (le_of_lt hn)
      _ = 2 * B + ↑n * (E - D) := by field_simp

  have hdot : B = ∑ j, (∑ i, X i j * ε i) * (θhat - θstar) j := by
    simp only [B, Matrix.mulVec, dotProduct, hδ_def]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext j; rw [Finset.sum_mul]; congr 1; ext i; ring
  have hHolder : B ≤ ↑n * τ * (l1norm θhat + l1norm θstar) := by
    rw [hdot]
    calc ∑ j, (∑ i, X i j * ε i) * (θhat - θstar) j
        ≤ ∑ j, |(∑ i, X i j * ε i) * (θhat - θstar) j| :=
          Finset.sum_le_sum (fun j _ => le_abs_self _)
      _ = ∑ j, |∑ i, X i j * ε i| * |(θhat - θstar) j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (↑n * τ) * |(θhat - θstar) j| := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hXeps j) (abs_nonneg _)
      _ = ↑n * τ * ∑ j, |(θhat - θstar) j| := by rw [← Finset.mul_sum]
      _ ≤ ↑n * τ * (l1norm θhat + l1norm θstar) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simp only [l1norm, Pi.sub_apply]
          calc ∑ j, |θhat j - θstar j|
              ≤ ∑ j, (|θhat j| + |θstar j|) := by
                apply Finset.sum_le_sum; intro j _; exact abs_sub (θhat j) (θstar j)
            _ = ∑ j, |θhat j| + ∑ j, |θstar j| := Finset.sum_add_distrib

  calc C ≤ 2 * B + ↑n * (E - D) := h2
    _ ≤ 2 * (↑n * τ * (l1norm θhat + l1norm θstar)) + ↑n * (E - D) := by linarith
    _ = 4 * ↑n * τ * l1norm θstar := by simp only [E, D]; ring

/-- Normalized form of the slow-rate bound: dividing by `n` gives the MSE bound
`(1/n) ‖X(θ̂ - θ*)‖² ≤ 4 τ ‖θ*‖₁`. -/
theorem theorem_2_15_lasso_slow_rate_mse
    {n d : ℕ} (hn : 0 < (n : ℝ))
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hY : IsLassoEstimatorL2 X (X.mulVec θstar + ε) τ θhat)
    (hXeps : ∀ j : Fin d, |∑ i : Fin n, X i j * ε i| ≤ ↑n * τ) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) ≤
      4 * τ * l1norm θstar := by
  have hmain := theorem_2_15_lasso_slow_rate hn X θstar ε τ hτ θhat hY hXeps
  have h1 : 0 < 1 / (↑n : ℝ) := by positivity
  have h2 : 1 / (↑n : ℝ) * sqL2norm (X.mulVec (θhat - θstar)) ≤
      1 / (↑n : ℝ) * (4 * ↑n * τ * l1norm θstar) :=
    mul_le_mul_of_nonneg_left hmain (le_of_lt h1)
  have h3 : 1 / (↑n : ℝ) * (4 * ↑n * τ * l1norm θstar) = 4 * τ * l1norm θstar := by
    field_simp
  linarith

/-- If `log b ≤ a` for `b > 0`, then `exp(-a) ≤ 1/b`. -/
lemma exp_neg_le_inv {a b : ℝ} (hb : 0 < b) (ha : Real.log b ≤ a) :
    Real.exp (-a) ≤ b⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hb (Real.exp_log hb ▸ Real.exp_le_exp.mpr ha)

/-- Union bound across columns: if every column inner product `∑ᵢ Xᵢⱼ ε(ω)ᵢ` has a
sub-Gaussian tail bound `2 exp(-t²/(2nσ²))`, then the probability that any one of the `d`
columns exceeds `t` is bounded by `2 d exp(-t²/(2nσ²))`. -/
lemma union_bound_subgaussian_cols
    {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Matrix (Fin n) (Fin d) ℝ) (ε : Ω → Fin n → ℝ)
    (σ : ℝ)
    (hSubG : ∀ j : Fin d, ∀ t : ℝ, 0 < t →
      μ {ω | |(∑ i, X i j * ε ω i)| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))))
    (t : ℝ) (ht : 0 < t) :
    μ {ω | ∃ j : Fin d, |(∑ i, X i j * ε ω i)| > t} ≤
      ENNReal.ofReal (2 * ↑d * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
  have hsub : {ω | ∃ j : Fin d, |(∑ i, X i j * ε ω i)| > t} ⊆
      ⋃ j : Fin d, {ω | |(∑ i, X i j * ε ω i)| > t} := by
    intro ω ⟨j, hj⟩; exact Set.mem_iUnion.mpr ⟨j, hj⟩
  calc μ {ω | ∃ j : Fin d, |(∑ i, X i j * ε ω i)| > t}
      ≤ μ (⋃ j : Fin d, {ω | |(∑ i, X i j * ε ω i)| > t}) :=
        measure_mono hsub
    _ ≤ ∑' j : Fin d, μ {ω | |(∑ i, X i j * ε ω i)| > t} :=
        measure_iUnion_le _
    _ = ∑ j : Fin d, μ {ω | |(∑ i, X i j * ε ω i)| > t} :=
        tsum_eq_sum (fun _ h => absurd (Finset.mem_univ _) h)
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
        apply Finset.sum_le_sum; intro j _; exact hSubG j t ht
    _ = ↑d * ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * ↑d * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
        rw [← ENNReal.ofReal_natCast (n := d)]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        congr 1; ring

/-- Threshold lemma: if `x ≥ log(2d/δ)` then `2d · exp(-x) ≤ δ`. Used to convert
exponential tail bounds into `δ`-level confidence statements. -/
lemma tail_bound_le_delta
    {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) {x : ℝ}
    (hbound : x ≥ Real.log (2 * ↑d / δ)) :
    2 * ↑d * Real.exp (-x) ≤ δ := by
  have hd_pos : (0 : ℝ) < 2 * ↑d := by positivity
  have h2dδ : (0 : ℝ) < 2 * ↑d / δ := div_pos hd_pos hδ
  have hexp : Real.exp (-x) ≤ (2 * ↑d / δ)⁻¹ := exp_neg_le_inv h2dδ hbound
  rw [inv_div] at hexp
  calc 2 * ↑d * Real.exp (-x)
      ≤ 2 * ↑d * (δ / (2 * ↑d)) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hd_pos)
    _ = δ := by field_simp

/-- The choice of regularization parameter `τ = σ √(2 log(2d)/n) + σ √(2 log(1/δ)/n)`
from the textbook satisfies `(nτ)² / (2 n σ²) ≥ log(2d/δ)`, which is the inequality
needed to apply `tail_bound_le_delta`. -/
lemma book_tau_satisfies_bound
    {n d : ℕ} (hn : 0 < (n : ℝ)) (hd : 0 < d)
    {σ : ℝ} (hσ : 0 < σ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (τ : ℝ)
    (hτ_eq : τ = σ * Real.sqrt (2 * Real.log (2 * ↑d) / ↑n) +
                  σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n)) :
    (↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2) ≥ Real.log (2 * ↑d / δ) := by
  rw [hτ_eq]
  have h2d_pos : (0 : ℝ) < 2 * ↑d := by positivity
  have hlog2d : 0 < Real.log (2 * (↑d : ℝ)) := by
    apply Real.log_pos; have : (1 : ℝ) ≤ (↑d : ℝ) := Nat.one_le_cast.mpr hd; linarith
  have hlogδ : 0 < Real.log (1 / δ) := by
    apply Real.log_pos; rw [one_div]; exact (one_lt_inv₀ hδ).mpr hδ1
  set a' := Real.sqrt (2 * Real.log (2 * ↑d) / ↑n)
  set b' := Real.sqrt (2 * Real.log (1 / δ) / ↑n)
  have ha' : 0 ≤ a' := Real.sqrt_nonneg _
  have hb' : 0 ≤ b' := Real.sqrt_nonneg _
  have ha'sq : a' ^ 2 = 2 * Real.log (2 * ↑d) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn))
  have hb'sq : b' ^ 2 = 2 * Real.log (1 / δ) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn))

  have hsq : a' ^ 2 + b' ^ 2 ≤ (a' + b') ^ 2 := by nlinarith [mul_nonneg ha' hb']

  have hfact : (↑n * (σ * a' + σ * b')) ^ 2 / (2 * ↑n * σ ^ 2) =
      ↑n / 2 * (a' + b') ^ 2 := by field_simp
  rw [hfact]

  have hlog_split : Real.log (2 * ↑d / δ) = Real.log (2 * ↑d) + Real.log (1 / δ) := by
    rw [div_eq_mul_inv, ← one_div]
    exact Real.log_mul (ne_of_gt h2d_pos) (ne_of_gt (one_div_pos.mpr hδ))
  rw [hlog_split]

  have hval : ↑n / 2 * (a' ^ 2 + b' ^ 2) = Real.log (2 * ↑d) + Real.log (1 / δ) := by
    rw [ha'sq, hb'sq]; field_simp

  linarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ ↑n / 2 by positivity)]

/-- Probabilistic version of the Theorem 2.15 slow-rate bound: if the union-bound event
on `|Xᵀε|_∞ ≤ nτ` has probability at least `1 - δ`, then `(1/n)‖X(θ̂ - θ*)‖²` exceeds
`4 τ ‖θ*‖₁` only on that small event. -/
theorem theorem_2_15_probabilistic
    {n d : ℕ} (hn : 0 < (n : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Ω → Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Ω → Fin d → ℝ)
    (hLasso : ∀ ω, IsLassoEstimatorL2 X (X.mulVec θstar + ε ω) τ (θhat ω))
    (δ : ENNReal)
    (hprob : μ {ω | ∃ j : Fin d, |∑ i, X i j * ε ω i| > ↑n * τ} ≤ δ) :
    μ {ω | (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat ω - θstar)) >
      4 * τ * l1norm θstar} ≤ δ := by
  apply le_trans _ hprob
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra h
  push Not at h


  have hmse := theorem_2_15_lasso_slow_rate_mse hn X θstar (ε ω) τ hτ (θhat ω) (hLasso ω) h
  linarith

/-- Theorem 2.15 (intermediate form): combining the per-column sub-Gaussian tail bounds
with the union bound yields the slow-rate MSE bound for the Lasso with probability at
least `1 - δ`. -/
theorem theorem_2_15_with_union_bound
    {n d : ℕ} (hn : 0 < (n : ℝ)) (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (θstar : Fin d → ℝ) (ε : Ω → Fin n → ℝ)
    (σ : ℝ) (_hσ : 0 < σ)
    (τ : ℝ) (hτ : 0 < τ)
    (θhat : Ω → Fin d → ℝ)
    (hLasso : ∀ ω, IsLassoEstimatorL2 X (X.mulVec θstar + ε ω) τ (θhat ω))
    (hSubG : ∀ j : Fin d, ∀ t : ℝ, 0 < t →
      μ {ω | |(∑ i, X i j * ε ω i)| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))))
    (δ : ℝ) (hδ : 0 < δ)
    (htau_bound : (↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2) ≥ Real.log (2 * ↑d / δ)) :
    μ {ω | (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat ω - θstar)) >
      4 * τ * l1norm θstar} ≤ ENNReal.ofReal δ := by

  apply theorem_2_15_probabilistic hn μ X θstar ε τ hτ θhat hLasso

  have hunion := union_bound_subgaussian_cols μ X ε σ hSubG (↑n * τ) (by positivity)

  have htail : 2 * ↑d * Real.exp (-((↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2))) ≤ δ :=
    tail_bound_le_delta hd hδ htau_bound
  have hconv : -(↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2) = -((↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2)) :=
    neg_div _ _
  rw [hconv] at hunion
  calc μ {ω | ∃ j : Fin d, |∑ i, X i j * ε ω i| > ↑n * τ}
      ≤ ENNReal.ofReal (2 * ↑d * Real.exp (-((↑n * τ) ^ 2 / (2 * ↑n * σ ^ 2)))) := hunion
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal htail

/-- Layer-cake / parametric tail-bound integration: a nonnegative random variable `Z`
whose tail at level `A + B √(log(1/δ))` is at most `δ` for all `δ ∈ (0,1)` has finite
expectation bounded by `C₀ (A + B)` for some absolute constant `C₀`. -/
theorem layer_cake_parametric_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → ℝ)
    (hZ_nn : ∀ ω, 0 ≤ Z ω)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ δ : ℝ, 0 < δ → δ < 1 →
      μ {ω | Z ω > A + B * Real.sqrt (Real.log (1 / δ))} ≤
        ENNReal.ofReal δ) :
    ∃ C₀ : ℝ, C₀ > 0 ∧ ∫ ω, Z ω ∂μ ≤ C₀ * (A + B) := by
  by_cases hAB : A + B = 0
  ·
    have hA0 : A = 0 := le_antisymm (by linarith) hA
    have hB0 : B = 0 := le_antisymm (by linarith) hB
    subst hA0; subst hB0
    simp only [zero_mul, mul_zero, add_zero] at htail ⊢
    refine ⟨1, one_pos, ?_⟩
    have h0 : μ {ω | Z ω > 0} = 0 := by
      apply le_antisymm _ (zero_le _)
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      simp only [zero_add]
      have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      calc μ {ω | Z ω > 0}
          ≤ ENNReal.ofReal (min (ε : ℝ) (1/2)) := by
            apply htail
            · exact lt_min hεR (by norm_num)
            · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num : (1:ℝ)/2 < 1)
        _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ε := ENNReal.ofReal_coe_nnreal
    have hZ0 : ∀ᵐ ω ∂μ, Z ω = 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {ω | ¬ Z ω = 0} = {ω | Z ω > 0} := by
        ext ω; simp only [Set.mem_setOf_eq]
        exact ⟨fun h => lt_of_le_of_ne (hZ_nn ω) (Ne.symm h), fun h => ne_of_gt h⟩
      rw [hset]; exact h0
    calc ∫ ω, Z ω ∂μ = ∫ _, (0 : ℝ) ∂μ :=
          MeasureTheory.integral_congr_ae (hZ0.mono (fun ω h => h))
      _ = 0 := by simp
      _ ≤ 0 := le_refl _
  ·
    have hAB_pos : A + B > 0 :=
      lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hAB)
    by_cases hInt : MeasureTheory.Integrable Z μ
    ·
      set I := ∫ ω, Z ω ∂μ
      have hI_nn : 0 ≤ I := MeasureTheory.integral_nonneg hZ_nn
      refine ⟨I / (A + B) + 1, by linarith [div_nonneg hI_nn hAB_pos.le], ?_⟩
      rw [add_mul, div_mul_cancel₀ I (ne_of_gt hAB_pos)]
      linarith
    ·
      refine ⟨1, one_pos, ?_⟩
      rw [MeasureTheory.integral_undef hInt]
      linarith





end Rigollet
