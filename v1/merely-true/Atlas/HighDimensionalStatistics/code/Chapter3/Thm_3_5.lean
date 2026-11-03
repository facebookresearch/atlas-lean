/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Atlas.HighDimensionalStatistics.code.Chapter2.Lemma_2_17
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Matrix Finset MeasureTheory

namespace Rigollet.Chapter3

/-- Squared Euclidean norm of a real vector `v : Fin n → ℝ`. -/
noncomputable def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- The squared Euclidean norm is nonnegative. -/
lemma sqNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Mean-squared error between an estimator `fhat` and a target `f` over
`n` design points: `MSE = (1/n) · Σᵢ (fhatᵢ − fᵢ)²`. -/
noncomputable def MSE_35 {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- The `ℓ₀` "sparsity" of a vector `θ`: the number of nonzero entries. -/
noncomputable def support_size_35 {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- The `ℓ¹` norm of a vector `θ : Fin M → ℝ`. -/
noncomputable def l1norm_35 {M : ℕ} (θ : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, |θ i|

/-- Least-squares objective for the design matrix `Φ` and response `Y`:
`(1/n) · ‖Y − Φθ‖²`. -/
noncomputable def lsObjective_35 {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (θ : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (Y i - (Φ.mulVec θ) i) ^ 2

/-- Lasso objective: least-squares loss plus `2τ‖θ‖₁` penalty. -/
noncomputable def lassoObjective_35 {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (τ : ℝ) (θ : Fin M → ℝ) : ℝ :=
  lsObjective_35 Y Φ θ + 2 * τ * l1norm_35 θ

/-- Triangle-style bound: `‖a − b‖² ≤ 2‖c − a‖² + 2‖c − b‖²`. -/
lemma sqNorm_diff_le {n : ℕ} (a b c : Fin n → ℝ) :
    sqNorm (a - b) ≤ 2 * sqNorm (c - a) + 2 * sqNorm (c - b) := by
  unfold sqNorm
  calc ∑ i, (a i - b i) ^ 2
      ≤ ∑ i, (2 * (c i - a i) ^ 2 + 2 * (c i - b i) ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          nlinarith [sq_nonneg (c i - a i + (c i - b i))]
    _ = 2 * ∑ i, (c i - a i) ^ 2 + 2 * ∑ i, (c i - b i) ^ 2 := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by simp [Pi.sub_apply]

/-- The cone condition relative to the support `S`: the off-support `ℓ¹` mass
of `Δ` is at most `3` times the on-support `ℓ¹` mass. -/
def ConeCondition {M : ℕ} (Δ : Fin M → ℝ) (S : Finset (Fin M)) :
    Prop :=
  ∑ j ∈ Finset.univ \ S, |Δ j| ≤ 3 * ∑ j ∈ S, |Δ j|

/-- The incoherence condition `INC(k)` of the design matrix `Φ`, used to
guarantee restricted invertibility on `k`-sparse vectors. -/
def INC_condition {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ) (k : ℕ) : Prop :=
  AssumptionINC Φ k

/-- Restricted `ℓ²` bound (consequence of Lemma 2.17 + cone condition):
on `S` with `|S| ≤ k`, `∑_{j ∈ S} Δⱼ² ≤ (2/n) · ‖ΦΔ‖²`. -/
theorem lemma_2_17_restricted_l2
    {n M : ℕ} (hn : 0 < n) (Φ : Matrix (Fin n) (Fin M) ℝ) (k : ℕ)
    (_hINC : INC_condition Φ k)
    (Δ : Fin M → ℝ) (S : Finset (Fin M))
    (hS_card : S.card ≤ k)
    (hCone : ConeCondition Δ S) :
    ∑ j ∈ S, (Δ j) ^ 2 ≤ 2 * sqNorm (Φ.mulVec Δ) / ↑n := by

  by_cases hk : k = 0
  · subst hk; simp only [Nat.le_zero] at hS_card
    rw [Finset.card_eq_zero] at hS_card; subst hS_card
    simp [sqNorm_nonneg, div_nonneg]

  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk

    have h := lemma_2_17_norm_equivalence hn Φ k hk_pos _hINC S hS_card Δ hCone

    have hdot : dotProduct (Φ.mulVec Δ) (Φ.mulVec Δ) = sqNorm (Φ.mulVec Δ) := by
      simp [dotProduct, sqNorm, sq]
    rw [hdot] at h

    have harith : 2 * (1 / (↑n : ℝ) * sqNorm (Φ.mulVec Δ)) =
        2 * sqNorm (Φ.mulVec Δ) / ↑n := by ring
    linarith

/-- The noise vector `ε` is coordinate-wise sub-Gaussian with parameter `σ`:
each `εᵢ` has MGF bounded by `exp(σ²s²/2)`. -/
def IsSubGaussianNoise {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σ ^ 2 * s ^ 2 / 2)

/-- A column-weighted linear combination `Σᵢ εᵢ Φᵢⱼ` of independent sub-Gaussian
noise variables is sub-Gaussian with parameter `n · σ²` whenever each column has
squared norm at most `n`. -/
theorem weighted_sum_isSubGaussian
    {Ω : Type*} {_ : MeasurableSpace Ω}
    {n M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (σ : ℝ)
    (hσ : 0 < σ) (hn : 0 < n)
    (hsubG : IsSubGaussianNoise ε σ μ)

    (hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)

    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)

    (hMeas : ∀ i : Fin n, Measurable (fun ω => ε ω i))

    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (j : Fin M) :
    IsSubGaussian (fun ω => ∑ i : Fin n, ε ω i * Φ i j) (↑n * σ ^ 2) μ := by

  have h16 := theorem_1_6_subgaussian_vector (X := fun i ω => ε ω i) (σsq := σ ^ 2)
    hsubG_full hIndep hMeas (fun i => Φ i j)

  have heq : (fun ω => ∑ i : Fin n, (fun i => Φ i j) i * (fun i ω => ε ω i) i ω) =
      (fun ω => ∑ i : Fin n, ε ω i * Φ i j) := by
    ext ω; congr 1; ext i; ring
  rw [heq] at h16

  have hle : σ ^ 2 * ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n * σ ^ 2 := by
    have hσsq : 0 ≤ σ ^ 2 := sq_nonneg σ
    calc σ ^ 2 * ∑ i, (Φ i j) ^ 2
        ≤ σ ^ 2 * ↑n := by
          apply mul_le_mul_of_nonneg_left (hColNorm j) hσsq
      _ = ↑n * σ ^ 2 := by ring

  exact ⟨h16.1, h16.2.1, h16.2.2.1, fun s => by
    calc ∫ ω, Real.exp (s * ∑ i, ε ω i * Φ i j) ∂μ
        ≤ Real.exp ((σ ^ 2 * ∑ i, (Φ i j) ^ 2) * s ^ 2 / 2) := h16.2.2.2 s
      _ ≤ Real.exp (↑n * σ ^ 2 * s ^ 2 / 2) := by
          apply Real.exp_le_exp_of_le
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right hle (sq_nonneg s)⟩

/-- Per-column tail bound: for each column `j`, the probability that
`|Σᵢ εᵢ Φᵢⱼ| > t` is at most `2 · exp(−t² / (2 n σ²))`. -/
theorem per_column_subG_tail_bound
    {Ω : Type*} {_ : MeasurableSpace Ω}
    {n M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (σ : ℝ)
    (hσ : 0 < σ) (hn : 0 < n)
    (hsubG : IsSubGaussianNoise ε σ μ)
    (hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (j : Fin M) (t : ℝ) (ht : 0 < t) :
    μ {ω | |∑ i : Fin n, ε ω i * Φ i j| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by

  have hSG := weighted_sum_isSubGaussian μ ε Φ σ hσ hn hsubG hsubG_full hIndep hMeas hColNorm j

  have hsplit : {ω | |∑ i : Fin n, ε ω i * Φ i j| > t} ⊆
      {ω | (∑ i : Fin n, ε ω i * Φ i j) > t} ∪
      {ω | (∑ i : Fin n, ε ω i * Φ i j) < -t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases lt_or_ge (∑ i, ε ω i * Φ i j) 0 with hneg | hpos
    · right; rw [abs_of_neg hneg] at hω; linarith
    · left; rw [abs_of_nonneg hpos] at hω; exact hω

  calc μ {ω | |∑ i : Fin n, ε ω i * Φ i j| > t}
      ≤ μ ({ω | (∑ i, ε ω i * Φ i j) > t} ∪
           {ω | (∑ i, ε ω i * Φ i j) < -t}) := measure_mono hsplit
    _ ≤ μ {ω | (∑ i, ε ω i * Φ i j) > t} +
        μ {ω | (∑ i, ε ω i * Φ i j) < -t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (↑n * σ ^ 2))))) +
        ENNReal.ofReal (Real.exp (-(t ^ 2 / (2 * (↑n * σ ^ 2))))) := by
        gcongr
        · exact lemma_1_3_upper_tail hSG t ht
        · exact lemma_1_3_lower_tail hSG t ht
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (↑n * σ ^ 2))))) := by
        rw [← two_mul, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
        congr 1; ring_nf

/-- If `b > 0` and `log b ≤ a`, then `exp(−a) ≤ b⁻¹`. -/
lemma exp_neg_le_inv' {a b : ℝ} (hb : 0 < b) (ha : Real.log b ≤ a) :
    Real.exp (-a) ≤ b⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hb (Real.exp_log hb ▸ Real.exp_le_exp.mpr ha)

/-- Union bound over the `M` columns: with the Lasso threshold
`2τ = 8σ√(2 log(2M)/n) + 8σ√(2 log(1/δ)/n)`, the event that every column
satisfies `|Σᵢ εᵢ Φᵢⱼ| ≤ nτ/4` has probability at least `1 − δ`. -/
theorem subG_max_union_bound
    {Ω : Type*} {_ : MeasurableSpace Ω}
    {n M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (σ τ δ : ℝ)
    (hσ : 0 < σ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hn : 0 < n) (hM : 0 < M)
    (hsubG : IsSubGaussianNoise ε σ μ)
    (hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                   8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n)) :
    μ {ω | ∀ (j : Fin M), |∑ i : Fin n, ε ω i * Φ i j| ≤ ↑n * τ / 4}
    ≥ ENNReal.ofReal (1 - δ) := by

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM

  have hτ_val : τ = 4 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    4 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n) := by linarith
  have hlog2M : 0 < Real.log (2 * ↑M) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ ↑M := Nat.one_le_cast.mpr hM
    linarith
  have hlog1d : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
  have ha_pos : 0 < Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) :=
    Real.sqrt_pos_of_pos (div_pos (by positivity) hn_pos)
  have hb_nn : 0 ≤ Real.sqrt (2 * Real.log (1 / δ) / ↑n) :=
    Real.sqrt_nonneg _
  have hτ_pos : 0 < τ := by rw [hτ_val]; positivity
  set t := ↑n * τ / 4 with ht_def
  have ht_pos : 0 < t := by positivity

  have hbad_le : μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ≤
      ENNReal.ofReal (2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
    have hsub : {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ⊆
        ⋃ j : Fin M, {ω | |∑ i, ε ω i * Φ i j| > t} := by
      intro ω ⟨j, hj⟩; exact Set.mem_iUnion.mpr ⟨j, hj⟩
    calc μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}
        ≤ μ (⋃ j : Fin M, {ω | |∑ i, ε ω i * Φ i j| > t}) := measure_mono hsub
      _ ≤ ∑' j : Fin M, μ {ω | |∑ i, ε ω i * Φ i j| > t} := measure_iUnion_le _
      _ = ∑ j : Fin M, μ {ω | |∑ i, ε ω i * Φ i j| > t} :=
          tsum_eq_sum (fun _ h => absurd (Finset.mem_univ _) h)
      _ ≤ ∑ _j : Fin M,
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          apply Finset.sum_le_sum; intro j _
          exact per_column_subG_tail_bound μ ε Φ σ hσ hn hsubG hsubG_full hIndep hMeas hColNorm j t ht_pos
      _ = ↑M * ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          rw [← ENNReal.ofReal_natCast (n := M)]
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
          congr 1; ring

  have h_tail : 2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2)) ≤ δ := by

    set a := Real.sqrt (2 * Real.log (2 * ↑M) / ↑n)
    set b := Real.sqrt (2 * Real.log (1 / δ) / ↑n)
    have ha_nn : 0 ≤ a := Real.sqrt_nonneg _
    have hb_nn : 0 ≤ b := Real.sqrt_nonneg _
    have ht_eq : t = ↑n * σ * (a + b) := by
      rw [ht_def, hτ_val]; ring
    have ha_sq : a ^ 2 = 2 * Real.log (2 * ↑M) / ↑n :=
      Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn_pos))
    have hb_sq : b ^ 2 = 2 * Real.log (1 / δ) / ↑n :=
      Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn_pos))

    have hsq : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha_nn hb_nn]

    have hfact : t ^ 2 / (2 * ↑n * σ ^ 2) = ↑n / 2 * (a + b) ^ 2 := by
      rw [ht_eq]; field_simp

    have hval : ↑n / 2 * (a ^ 2 + b ^ 2) = Real.log (2 * ↑M) + Real.log (1 / δ) := by
      rw [ha_sq, hb_sq]; field_simp

    have h2M_pos : (0 : ℝ) < 2 * ↑M := by positivity
    have hlog_split : Real.log (2 * ↑M / δ) = Real.log (2 * ↑M) + Real.log (1 / δ) := by
      rw [div_eq_mul_inv, ← one_div]
      exact Real.log_mul (ne_of_gt h2M_pos) (ne_of_gt (one_div_pos.mpr hδ_pos))

    have hge : t ^ 2 / (2 * ↑n * σ ^ 2) ≥ Real.log (2 * ↑M / δ) := by
      rw [hfact, hlog_split]
      nlinarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ ↑n / 2 by positivity)]

    have h2Mδ : (0 : ℝ) < 2 * ↑M / δ := div_pos h2M_pos hδ_pos
    have hexp_neg_rw : -t ^ 2 / (2 * ↑n * σ ^ 2) = -(t ^ 2 / (2 * ↑n * σ ^ 2)) := neg_div _ _
    rw [hexp_neg_rw]
    have hexp : Real.exp (-(t ^ 2 / (2 * ↑n * σ ^ 2))) ≤ (2 * ↑M / δ)⁻¹ :=
      exp_neg_le_inv' h2Mδ hge
    rw [inv_div] at hexp
    calc 2 * ↑M * Real.exp (-(t ^ 2 / (2 * ↑n * σ ^ 2)))
        ≤ 2 * ↑M * (δ / (2 * ↑M)) := by
          apply mul_le_mul_of_nonneg_left hexp (le_of_lt h2M_pos)
      _ = δ := by field_simp

  have hbad_le_delta : μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ≤
      ENNReal.ofReal δ :=
    le_trans hbad_le (ENNReal.ofReal_le_ofReal h_tail)

  have hgood_eq : {ω | ∀ (j : Fin M), |∑ i : Fin n, ε ω i * Φ i j| ≤ t} =
      {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt]
  rw [hgood_eq]

  set bad := {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}

  have h_sum : 1 ≤ μ bad + μ badᶜ := by
    rw [← measure_univ (μ := μ)]
    calc μ Set.univ = μ (bad ∪ badᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ bad + μ badᶜ := measure_union_le bad badᶜ

  rw [show ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ from by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_sub _ (le_of_lt hδ_pos)]

  calc 1 - ENNReal.ofReal δ ≤ 1 - μ bad := tsub_le_tsub_left hbad_le_delta _
    _ ≤ μ badᶜ := by
        have := tsub_le_iff_left.mpr h_sum
        exact this

/-- Rewriting the least-squares objective as `(1/n) · ‖Y − Φθ‖²`. -/
lemma lsObjective_eq_sqNorm {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ) (θ : Fin M → ℝ) :
    lsObjective_35 Y Φ θ = (1 / (↑n : ℝ)) * sqNorm (Y - Φ.mulVec θ) := by
  unfold lsObjective_35 sqNorm; simp [Pi.sub_apply]

/-- Model expansion identity: with `Y = f + ε`, the difference of squared errors
on `f` decomposes into the corresponding `Y`-difference plus a `2 · ⟨ε, Φ(θ̂ − θ)⟩`
cross term. -/
lemma sqNorm_model_expansion {n M : ℕ} (f ε_val : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (θhat θ : Fin M → ℝ) (Y : Fin n → ℝ) (hModel : ∀ i, Y i = f i + ε_val i) :
    sqNorm (f - Φ.mulVec θhat) - sqNorm (f - Φ.mulVec θ) =
    sqNorm (Y - Φ.mulVec θhat) - sqNorm (Y - Φ.mulVec θ) +
    2 * (∑ i, ε_val i * (Φ.mulVec (θhat - θ)) i) := by
  unfold sqNorm; simp only [Pi.sub_apply]
  rw [show (∑ i, (Y i - (Φ.mulVec θhat) i) ^ 2) - (∑ i, (Y i - (Φ.mulVec θ) i) ^ 2) =
       ∑ i, ((Y i - (Φ.mulVec θhat) i) ^ 2 - (Y i - (Φ.mulVec θ) i) ^ 2) from
       by rw [← Finset.sum_sub_distrib]]
  rw [show (∑ i, (f i - (Φ.mulVec θhat) i) ^ 2) - (∑ i, (f i - (Φ.mulVec θ) i) ^ 2) =
       ∑ i, ((f i - (Φ.mulVec θhat) i) ^ 2 - (f i - (Φ.mulVec θ) i) ^ 2) from
       by rw [← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp only [mulVec_sub, Pi.sub_apply]; rw [hModel i]; ring

set_option maxRecDepth 2048 in

/-- Support-restricted chain inequality: under INC and `k`-sparsity of `θ`,
the Lasso-residual `ℓ¹` mass and norm-comparison terms are dominated by
`α/2 · ‖Φ(θ̂ − θ)‖² + 16 τ² n |θ|₀ / α`. -/
lemma support_restricted_chain
    {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ)
    (τ α : ℝ) (k : ℕ)
    (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hk : 0 < k)
    (_hτ_nonneg : 0 ≤ τ)
    (θhat θ : Fin M → ℝ)
    (_hINC : INC_condition Φ k)
    (_hSparse : support_size_35 θ ≤ k) :
    ↑n * τ / 2 * l1norm_35 (θhat - θ) + 2 * ↑n * τ * (l1norm_35 θ - l1norm_35 θhat) ≤
      α / 2 * sqNorm (Φ.mulVec (θhat - θ)) +
        16 * τ ^ 2 * (n : ℝ) * ↑(support_size_35 θ) / α := by

  set S := Finset.univ.filter (fun i => θ i ≠ 0) with hS_def
  set Δ := θhat - θ with hΔ_def
  have hθhat : θhat = θ + Δ := by simp [Δ]
  have hScard : S.card ≤ k := _hSparse
  have hS_sub : S ⊆ Finset.univ := Finset.filter_subset _ _

  set sS := ∑ j ∈ S, |Δ j|
  set sSc := ∑ j ∈ Finset.univ \ S, |Δ j|
  set B := sqNorm (Φ.mulVec Δ)
  have hn_nn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
  have hsS_nn : 0 ≤ sS := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsSc_nn : 0 ≤ sSc := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnτ : 0 ≤ ↑n * τ := mul_nonneg hn_nn _hτ_nonneg

  have hl1_split : l1norm_35 Δ = sS + sSc := by
    simp only [l1norm_35, sS, sSc, ← Finset.sum_sdiff hS_sub]; ring

  have hOff : ∀ j ∈ Finset.univ \ S, θ j = 0 := by
    intro j hj; simp [S, Finset.mem_sdiff, Finset.mem_filter] at hj; exact hj

  have hTri : l1norm_35 θ - l1norm_35 θhat ≤ sS - sSc := by
    rw [show l1norm_35 θhat = l1norm_35 (θ + Δ) from by rw [hθhat]]
    unfold l1norm_35
    rw [show ∑ i : Fin M, |θ i| = ∑ j ∈ S, |θ j| + ∑ j ∈ Finset.univ \ S, |θ j| from
          by rw [← Finset.sum_sdiff hS_sub]; ring,
        show ∑ i : Fin M, |(θ + Δ) i| = ∑ j ∈ S, |(θ + Δ) j| + ∑ j ∈ Finset.univ \ S, |(θ + Δ) j| from
          by rw [← Finset.sum_sdiff hS_sub]; ring,
        show ∑ j ∈ Finset.univ \ S, |θ j| = 0 from
          Finset.sum_eq_zero fun j hj => by simp [hOff j hj],
        show ∑ j ∈ Finset.univ \ S, |(θ + Δ) j| = sSc from
          Finset.sum_congr rfl fun j hj => by simp [Pi.add_apply, hOff j hj]]
    simp only [add_zero]
    suffices h : ∑ j ∈ S, |θ j| ≤ ∑ j ∈ S, |(θ + Δ) j| + sS by linarith
    calc ∑ j ∈ S, |θ j|
        = ∑ j ∈ S, |(θ + Δ) j - Δ j| := by congr 1; ext j; simp [Pi.add_apply]
      _ ≤ ∑ j ∈ S, (|(θ + Δ) j| + |Δ j|) := Finset.sum_le_sum fun j _ => by
          calc |(θ + Δ) j - Δ j| ≤ |(θ + Δ) j| + |-(Δ j)| := abs_add_le _ _
            _ = |(θ + Δ) j| + |Δ j| := by rw [abs_neg]
      _ = ∑ j ∈ S, |(θ + Δ) j| + sS := by rw [Finset.sum_add_distrib]

  have hLHS : ↑n * τ / 2 * l1norm_35 Δ + 2 * ↑n * τ * (l1norm_35 θ - l1norm_35 θhat)
      ≤ 5 / 2 * (↑n * τ) * sS - 3 / 2 * (↑n * τ) * sSc := by
    rw [hl1_split]; nlinarith

  have hRHS_nn : 0 ≤ α / 2 * B + 16 * τ ^ 2 * ↑n * ↑(support_size_35 θ) / α :=
    add_nonneg (mul_nonneg (div_nonneg (le_of_lt _hα_pos) (by norm_num)) hB_nn)
      (div_nonneg (by positivity) (le_of_lt _hα_pos))

  by_cases hCone : ConeCondition Δ S
  ·

    have hCS : sS ^ 2 ≤ ↑S.card * ∑ j ∈ S, (Δ j) ^ 2 := by
      have h := @sq_sum_le_card_mul_sum_sq (Fin M) ℝ _ _ _ _ (s := S) (f := fun j => |Δ j|)
      simp only [sq_abs] at h; exact h

    have hNsS2 : ↑n * sS ^ 2 ≤ 2 * ↑S.card * B := by
      by_cases hn0 : n = 0
      · subst hn0; simp only [Nat.cast_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg _)) hB_nn
      · have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        have hne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos

        have hL217 := lemma_2_17_restricted_l2 (Nat.pos_of_ne_zero hn0) Φ k _hINC Δ S hScard hCone
        have h1 : sS ^ 2 ≤ ↑S.card * (2 * B / ↑n) :=
          le_trans hCS (mul_le_mul_of_nonneg_left hL217 (Nat.cast_nonneg S.card))
        have h2 : ↑n * sS ^ 2 ≤ ↑n * (↑S.card * (2 * B / ↑n)) :=
          mul_le_mul_of_nonneg_left h1 hn_nn
        have h3 : ↑n * (↑S.card * (2 * B / ↑n)) = 2 * ↑S.card * B := by
          rw [div_eq_mul_inv]
          have : ↑n * (↑S.card * (2 * B * (↑n)⁻¹))
               = ↑S.card * 2 * B * (↑n * (↑n)⁻¹) := by ring
          rw [this, mul_inv_cancel₀ hne, mul_one]; ring
        linarith

    have hYoung : 4 * ↑n * τ * sS ≤ α / 2 * B + 16 * τ ^ 2 * ↑n * ↑S.card / α := by
      by_cases hn0 : n = 0
      ·
        subst hn0; simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
        exact mul_nonneg (div_nonneg (le_of_lt _hα_pos) (by norm_num : (0:ℝ) ≤ 2)) hB_nn
      · by_cases hsc0 : S.card = 0
        ·
          have hsS0 : sS = 0 := by
            have : S = ∅ := Finset.card_eq_zero.mp hsc0
            show ∑ j ∈ S, |Δ j| = 0
            rw [this]; exact Finset.sum_empty
          rw [hsS0]; simp only [mul_zero]
          exact add_nonneg
            (mul_nonneg (div_nonneg (le_of_lt _hα_pos) (by norm_num : (0:ℝ) ≤ 2)) hB_nn)
            (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16)
              (sq_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (le_of_lt _hα_pos))
        · have hsc_pos : (0 : ℝ) < ↑S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsc0)
          have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
          have hne_α : (α : ℝ) ≠ 0 := ne_of_gt _hα_pos
          have hne_n : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have hne_sc : (↑S.card : ℝ) ≠ 0 := ne_of_gt hsc_pos

          suffices h : 8 * α * ↑n * τ * sS ≤ α ^ 2 * B + 32 * τ ^ 2 * ↑n * ↑S.card by
            have h2α : (0 : ℝ) < 2 * α := mul_pos (by norm_num : (0:ℝ) < 2) _hα_pos
            rw [show α / 2 * B + 16 * τ ^ 2 * ↑n * ↑S.card / α =
                 (α ^ 2 * B + 32 * τ ^ 2 * ↑n * ↑S.card) / (2 * α) from by
                  rw [div_mul_eq_mul_div, div_add_div _ _ two_ne_zero hne_α]
                  congr 1; ring,
                show 4 * ↑n * τ * sS = 8 * α * ↑n * τ * sS / (2 * α) from by
                  rw [eq_div_iff (ne_of_gt h2α)]; ring]
            exact div_le_div_of_nonneg_right h (le_of_lt h2α)
          have hkey : 0 ≤ α ^ 2 / (2 * ↑S.card) :=
            div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hsc_pos))
          nlinarith [sq_nonneg (α * sS - 8 * τ * ↑S.card),
                     mul_le_mul_of_nonneg_left hNsS2 hkey]

    calc ↑n * τ / 2 * l1norm_35 (θhat - θ) + 2 * ↑n * τ * (l1norm_35 θ - l1norm_35 θhat)
        ≤ 5 / 2 * (↑n * τ) * sS - 3 / 2 * (↑n * τ) * sSc := hLHS
      _ ≤ 5 / 2 * (↑n * τ) * sS := by nlinarith [mul_nonneg hnτ hsSc_nn]
      _ ≤ 4 * ↑n * τ * sS := by nlinarith [mul_nonneg hnτ hsS_nn]
      _ ≤ α / 2 * B + 16 * τ ^ 2 * ↑n * ↑S.card / α := hYoung
      _ = α / 2 * sqNorm (Φ.mulVec (θhat - θ)) +
            16 * τ ^ 2 * ↑n * ↑(support_size_35 θ) / α := by rfl
  ·
    unfold ConeCondition at hCone
    have hCone' : 3 * sS < sSc := by linarith [not_le.mp hCone]
    have hLHS_neg : 5 / 2 * (↑n * τ) * sS - 3 / 2 * (↑n * τ) * sSc ≤ 0 := by
      nlinarith [mul_nonneg hnτ hsS_nn]
    linarith

/-- Stage A: combining the Lasso optimality, the noise concentration event,
INC, and `k`-sparsity, the prediction-error gap is bounded by
`α/2 · ‖Φ(θ̂ − θ)‖² + 16τ² n |θ|₀ / α`. -/
theorem stage_A_chain_bound
    {n M : ℕ}
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (Y f : Fin n → ℝ) (ε_val : Fin n → ℝ)
    (τ α : ℝ) (k : ℕ)
    (_hα_pos : 0 < α) (_hα_lt : α < 1)
    (_hk : 0 < k)
    (_hτ_nonneg : 0 ≤ τ)
    (θhat θ : Fin M → ℝ)

    (_hModel : ∀ i, Y i = f i + ε_val i)

    (_hLasso : lassoObjective_35 Y Φ τ θhat ≤ lassoObjective_35 Y Φ τ θ)

    (_hConc : ∀ (v : Fin M → ℝ),
        2 * (∑ i : Fin n, ε_val i * (Φ.mulVec v) i) ≤
          ↑n * τ / 2 * l1norm_35 v)

    (_hINC : INC_condition Φ k)

    (_hSparse : support_size_35 θ ≤ k) :
    sqNorm (f - Φ.mulVec θhat) -
        sqNorm (f - Φ.mulVec θ) ≤
      α / 2 * sqNorm (Φ.mulVec (θhat - θ)) +
        16 * τ ^ 2 * (n : ℝ) *
          ↑(support_size_35 θ) / α := by

  suffices h_key : sqNorm (f - Φ.mulVec θhat) - sqNorm (f - Φ.mulVec θ) ≤
      ↑n * τ / 2 * l1norm_35 (θhat - θ) +
        2 * ↑n * τ * (l1norm_35 θ - l1norm_35 θhat) by
    linarith [support_restricted_chain Φ τ α k _hα_pos _hα_lt _hk _hτ_nonneg θhat θ _hINC _hSparse]

  rw [sqNorm_model_expansion f ε_val Φ θhat θ Y _hModel]

  have hConc_applied := _hConc (θhat - θ)

  rw [lassoObjective_35, lassoObjective_35,
      lsObjective_eq_sqNorm, lsObjective_eq_sqNorm] at _hLasso

  have hYdiff_scaled :
      (1 / ↑n) * (sqNorm (Y - Φ.mulVec θhat) - sqNorm (Y - Φ.mulVec θ)) ≤
        2 * τ * (l1norm_35 θ - l1norm_35 θhat) := by linarith

  by_cases hn : (↑n : ℝ) = 0
  ·
    have hn0 : n = 0 := by exact_mod_cast hn
    subst hn0
    simp only [sqNorm, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
               Nat.cast_zero, zero_mul, zero_div, add_zero, mul_zero] at *
    linarith
  ·
    have hn_pos : (0 : ℝ) < ↑n := by positivity
    have hYdiff : sqNorm (Y - Φ.mulVec θhat) - sqNorm (Y - Φ.mulVec θ) ≤
        2 * ↑n * τ * (l1norm_35 θ - l1norm_35 θhat) := by
      have h := mul_le_mul_of_nonneg_left hYdiff_scaled (le_of_lt hn_pos)
      have h1 : ↑n * ((1 / ↑n) *
          (sqNorm (Y - Φ.mulVec θhat) - sqNorm (Y - Φ.mulVec θ))) =
          sqNorm (Y - Φ.mulVec θhat) - sqNorm (Y - Φ.mulVec θ) := by
        field_simp
      linarith [h1]
    linarith

/-- Stage B (sparse oracle form): converting the chain inequality from Stage A
into `(1 − α) ‖f − Φθ̂‖² ≤ (1 + α) ‖f − Φθ‖² + 16 τ² n |θ|₀ / α`. -/
theorem theorem_3_5_lasso_sparse_oracle
    {n M : ℕ}
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (_Y f : Fin n → ℝ) (τ α : ℝ)
    (hα_pos : 0 < α) (_hα_lt : α < 1)
    (θhat θ : Fin M → ℝ)

    (hChain : sqNorm (f - Φ.mulVec θhat) -
        sqNorm (f - Φ.mulVec θ) ≤
      α / 2 * sqNorm (Φ.mulVec (θhat - θ)) +
        16 * τ ^ 2 * (n : ℝ) *
          ↑(support_size_35 θ) / α) :
    (1 - α) * sqNorm (f - Φ.mulVec θhat) ≤
      (1 + α) * sqNorm (f - Φ.mulVec θ) +
        16 * τ ^ 2 * (n : ℝ) *
          ↑(support_size_35 θ) / α := by

  set A := sqNorm (f - Φ.mulVec θhat)
  set B := sqNorm (f - Φ.mulVec θ)
  set D := sqNorm (Φ.mulVec (θhat - θ))
  set C := 16 * τ ^ 2 * (n : ℝ) * ↑(support_size_35 θ) / α

  have hTri : D ≤ 2 * A + 2 * B := by
    show sqNorm (Φ.mulVec (θhat - θ)) ≤ _
    rw [show Φ.mulVec (θhat - θ) =
        Φ.mulVec θhat - Φ.mulVec θ from by simp [mulVec_sub]]
    exact sqNorm_diff_le _ _ f

  have hαD : α / 2 * D ≤ α * A + α * B :=
    calc α / 2 * D ≤ α / 2 * (2 * A + 2 * B) :=
          mul_le_mul_of_nonneg_left hTri (by linarith)
      _ = α * A + α * B := by ring

  linarith

/-- Hölder-type consequence of the column event: a uniform per-column bound
`|⟨ε, Φ_{·j}⟩| ≤ B` implies `2 |⟨ε, Φv⟩| ≤ 2 B · ‖v‖₁`. -/
lemma column_event_implies_holder
    {n M : ℕ}
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (ε_val : Fin n → ℝ)
    (B : ℝ)
    (hcol : ∀ j : Fin M, |∑ i : Fin n, ε_val i * Φ i j| ≤ B)
    (v : Fin M → ℝ) :
    2 * |∑ i : Fin n, ε_val i * (Φ.mulVec v) i| ≤
      2 * B * l1norm_35 v := by
  suffices h : |∑ i : Fin n, ε_val i * (Φ.mulVec v) i| ≤ B * l1norm_35 v by
    nlinarith [abs_nonneg (∑ i : Fin n, ε_val i * (Φ.mulVec v) i)]

  have expand : ∑ i : Fin n, ε_val i * (Φ.mulVec v) i =
      ∑ j : Fin M, v j * (∑ i : Fin n, ε_val i * Φ i j) := by
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext j
    congr 1; ext i
    ring
  rw [expand]
  calc |∑ j : Fin M, v j * (∑ i : Fin n, ε_val i * Φ i j)|
      ≤ ∑ j : Fin M, |v j * (∑ i : Fin n, ε_val i * Φ i j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin M, |v j| * |∑ i : Fin n, ε_val i * Φ i j| := by
        congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j : Fin M, |v j| * B := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = B * l1norm_35 v := by
        unfold l1norm_35; rw [Finset.mul_sum]; congr 1; ext j; ring

/-- Conversion of the Stage-B bound into the textbook MSE form, with the
`16 τ²` factor replaced by `1024 σ²` and the noise threshold split into
`log(eM)` and `log(1/δ)` contributions. -/
theorem tau_to_mse_conversion
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (θhat θ' : Fin M → ℝ)
    (σ τ α δ : ℝ)
    (_hσ : 0 < σ) (_hα_pos : 0 < α) (_hα_lt : α < 1)
    (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (_hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n))
    (_hStageB : (1 - α) * sqNorm (f - Φ.mulVec θhat) ≤
        (1 + α) * sqNorm (f - Φ.mulVec θ') +
          16 * τ ^ 2 * ↑n * ↑(support_size_35 θ') / α) :
    MSE_35 (Φ *ᵥ θhat) f ≤
    (1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ') f +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
        ↑(support_size_35 θ') *
        Real.log (Real.exp 1 * ↑M) +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
        ↑(support_size_35 θ') *
        Real.log (1 / δ) := by

  have hnn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM
  have h1α : 0 < 1 - α := by linarith

  have hMSE_hat : MSE_35 (Φ *ᵥ θhat) f = (1 / (↑n : ℝ)) * sqNorm (f - Φ.mulVec θhat) := by
    simp only [MSE_35, sqNorm, Pi.sub_apply]
    congr 1; congr 1; ext i; ring
  have hMSE_prime : MSE_35 (Φ *ᵥ θ') f = (1 / (↑n : ℝ)) * sqNorm (f - Φ.mulVec θ') := by
    simp only [MSE_35, sqNorm, Pi.sub_apply]
    congr 1; congr 1; ext i; ring
  rw [hMSE_hat, hMSE_prime]

  set A := sqNorm (f - Φ.mulVec θhat)
  set B := sqNorm (f - Φ.mulVec θ')
  set s := (↑(support_size_35 θ') : ℝ)

  set a := Real.sqrt (2 * Real.log (2 * ↑M) / ↑n)
  set b := Real.sqrt (2 * Real.log (1 / δ) / ↑n)
  have hτ_val : τ = 4 * σ * (a + b) := by linarith
  have hlog2M : 0 < Real.log (2 * ↑M) := by
    apply Real.log_pos; linarith [show (1 : ℝ) ≤ ↑M from Nat.one_le_cast.mpr hM]
  have hlog1d : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ _hδ_pos]; linarith
  have ha_sq : a ^ 2 = 2 * Real.log (2 * ↑M) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hnn_pos))
  have hb_sq : b ^ 2 = 2 * Real.log (1 / δ) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hnn_pos))
  set L := Real.log (Real.exp 1 * ↑M)
  set Ld := Real.log (1 / δ)

  have h16tau_bound : 16 * τ ^ 2 ≤ 1024 * σ ^ 2 * (L + Ld) / ↑n := by
    have h16tau_eq : 16 * τ ^ 2 = 256 * σ ^ 2 * (a + b) ^ 2 := by rw [hτ_val]; ring
    have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    have h_expand : 512 * σ ^ 2 * (a ^ 2 + b ^ 2) =
        1024 * σ ^ 2 * (Real.log (2 * ↑M) + Ld) / ↑n := by
      rw [ha_sq, hb_sq]; field_simp; ring
    have h_log_mono : Real.log (2 * ↑M) ≤ L := by
      apply Real.log_le_log (by positivity)
      nlinarith [Real.exp_one_gt_two]
    calc 16 * τ ^ 2 = 256 * σ ^ 2 * (a + b) ^ 2 := h16tau_eq
      _ ≤ 256 * σ ^ 2 * (2 * (a ^ 2 + b ^ 2)) := by nlinarith [sq_nonneg σ]
      _ = 512 * σ ^ 2 * (a ^ 2 + b ^ 2) := by ring
      _ = 1024 * σ ^ 2 * (Real.log (2 * ↑M) + Ld) / ↑n := h_expand
      _ ≤ 1024 * σ ^ 2 * (L + Ld) / ↑n := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hnn_pos)
          nlinarith [sq_nonneg σ]

  have h16tau_n : 16 * τ ^ 2 * ↑n ≤ 1024 * σ ^ 2 * (L + Ld) := by
    have h := mul_le_mul_of_nonneg_right h16tau_bound (le_of_lt hnn_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hnn_pos)] at h

  have h_tail_bound : 16 * τ ^ 2 * ↑n * s / α ≤ 1024 * σ ^ 2 * (L + Ld) * s / α := by
    apply div_le_div_of_nonneg_right _ (le_of_lt _hα_pos)
    apply mul_le_mul_of_nonneg_right h16tau_n (Nat.cast_nonneg' (support_size_35 θ'))

  have hStageB' : (1 - α) * A ≤ (1 + α) * B + 1024 * σ ^ 2 * (L + Ld) * s / α := by linarith

  have hA_bound : A ≤ (1 + α) / (1 - α) * B + 1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α)) := by
    have h_rhs_eq : (1 + α) / (1 - α) * B + 1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α)) =
        ((1 + α) * B + 1024 * σ ^ 2 * (L + Ld) * s / α) / (1 - α) := by
      field_simp
    rw [h_rhs_eq, le_div_iff₀ h1α]
    linarith

  have hMSE_bound : (1 / (↑n : ℝ)) * A ≤ (1 + α) / (1 - α) * ((1 / (↑n : ℝ)) * B) +
      1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α) * ↑n) := by
    have h1 := mul_le_mul_of_nonneg_left hA_bound (show (0 : ℝ) ≤ 1 / ↑n by positivity)
    have h2 : (1 / (↑n : ℝ)) * ((1 + α) / (1 - α) * B +
        1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α))) =
        (1 + α) / (1 - α) * ((1 / (↑n : ℝ)) * B) +
        1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α) * ↑n) := by field_simp

    linarith

  have h_split : 1024 * σ ^ 2 * (L + Ld) * s / (α * (1 - α) * ↑n) =
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) * s * L +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) * s * Ld := by ring
  linarith

/-- Variant of `tau_to_mse_conversion` taking the already-split Stage-B hypothesis
(with the `log(eM) · |θ|₀ + log(1/δ)` term packaged together). -/
theorem tau_to_mse_conversion_split
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (θhat θ' : Fin M → ℝ)
    (σ α δ : ℝ)
    (_hσ : 0 < σ) (_hα_pos : 0 < α) (_hα_lt : α < 1)
    (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)

    (_hStageB_split : (1 - α) * sqNorm (f - Φ.mulVec θhat) ≤
        (1 + α) * sqNorm (f - Φ.mulVec θ') +
          (1024 * σ ^ 2 * Real.log (Real.exp 1 * ↑M) *
            ↑(support_size_35 θ') +
           1024 * σ ^ 2 * Real.log (1 / δ)) / α) :
    MSE_35 (Φ *ᵥ θhat) f ≤
    (1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ') f +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
        ↑(support_size_35 θ') *
        Real.log (Real.exp 1 * ↑M) +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
        Real.log (1 / δ) := by

  have hnn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have _hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM
  have h1α : 0 < 1 - α := by linarith

  have hMSE_hat : MSE_35 (Φ *ᵥ θhat) f = (1 / (↑n : ℝ)) * sqNorm (f - Φ.mulVec θhat) := by
    simp only [MSE_35, sqNorm, Pi.sub_apply]
    congr 1; congr 1; ext i; ring
  have hMSE_prime : MSE_35 (Φ *ᵥ θ') f = (1 / (↑n : ℝ)) * sqNorm (f - Φ.mulVec θ') := by
    simp only [MSE_35, sqNorm, Pi.sub_apply]
    congr 1; congr 1; ext i; ring
  rw [hMSE_hat, hMSE_prime]
  set A := sqNorm (f - Φ.mulVec θhat)
  set Bsq := sqNorm (f - Φ.mulVec θ')
  set s := (↑(support_size_35 θ') : ℝ)
  set L := Real.log (Real.exp 1 * ↑M)
  set Ld := Real.log (1 / δ)

  have hA_bound : A ≤ (1 + α) / (1 - α) * Bsq +
      (1024 * σ ^ 2 * L * s + 1024 * σ ^ 2 * Ld) / (α * (1 - α)) := by
    have h_rhs_eq : (1 + α) / (1 - α) * Bsq +
        (1024 * σ ^ 2 * L * s + 1024 * σ ^ 2 * Ld) / (α * (1 - α)) =
        ((1 + α) * Bsq + (1024 * σ ^ 2 * L * s + 1024 * σ ^ 2 * Ld) / α) / (1 - α) := by
      field_simp
    rw [h_rhs_eq, le_div_iff₀ h1α]
    linarith

  have hMSE_bound : (1 / (↑n : ℝ)) * A ≤ (1 + α) / (1 - α) * ((1 / (↑n : ℝ)) * Bsq) +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) * s * L +
      1024 * σ ^ 2 / (α * (1 - α) * ↑n) * Ld := by
    have h1 := mul_le_mul_of_nonneg_left hA_bound (show (0 : ℝ) ≤ 1 / ↑n by positivity)
    have h2 : (1 / (↑n : ℝ)) * ((1 + α) / (1 - α) * Bsq +
        (1024 * σ ^ 2 * L * s + 1024 * σ ^ 2 * Ld) / (α * (1 - α))) =
        (1 + α) / (1 - α) * ((1 / (↑n : ℝ)) * Bsq) +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) * s * L +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) * Ld := by
      field_simp; ring
    linarith
  linarith

/-- From a uniform per-column event `|⟨ε, Φ_{·j}⟩| ≤ σ √(2n log(2M/δ))`,
together with Lasso optimality, INC, and `k`-sparsity of `θ'`, derive the
Stage-B oracle inequality
`(1 − α)‖f − Φθ̂‖² ≤ (1 + α)‖f − Φθ'‖² + 16 τ² n |θ'|₀ / α`. -/
lemma column_event_to_stageB_split
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (Y : Fin n → ℝ)
    (ε_val : Fin n → ℝ)
    (θhat θ' : Fin M → ℝ)
    (σ τ α δ : ℝ)
    (hσ : 0 < σ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (k : ℕ) (hk : 0 < k)
    (hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n))
    (hModel : ∀ i, Y i = f i + ε_val i)
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (hINC : INC_condition Φ k)
    (hLasso : lassoObjective_35 Y Φ τ θhat ≤ lassoObjective_35 Y Φ τ θ')
    (hθ'_sparse : support_size_35 θ' ≤ k)

    (hcol : ∀ j : Fin M, |∑ i : Fin n, ε_val i * Φ i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ))) :
    (1 - α) * sqNorm (f - Φ.mulVec θhat) ≤
        (1 + α) * sqNorm (f - Φ.mulVec θ') +
          16 * τ ^ 2 * ↑n * ↑(support_size_35 θ') / α := by

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM

  have hτ_nonneg : 0 ≤ τ := by
    have : 0 ≤ 2 * τ := by
      rw [hτ]; apply add_nonneg <;> apply mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    linarith

  set B := σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ)) with hB_def
  have hHolder : ∀ v : Fin M → ℝ,
      2 * |∑ i : Fin n, ε_val i * (Φ.mulVec v) i| ≤ 2 * B * l1norm_35 v :=
    column_event_implies_holder Φ ε_val B hcol

  have h4B_le_nτ : 4 * B ≤ ↑n * τ := by

    have hτ_val : τ = 4 * σ * (Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
        Real.sqrt (2 * Real.log (1 / δ) / ↑n)) := by linarith
    rw [hτ_val, hB_def]

    have hlog_split : Real.log (2 * ↑M / δ) = Real.log (2 * ↑M) + Real.log (1 / δ) := by
      rw [div_eq_mul_inv, ← one_div, Real.log_mul (by positivity) (by positivity)]
    have hlog2M_pos : 0 < Real.log (2 * ↑M) := by
      apply Real.log_pos; linarith [show (1 : ℝ) ≤ ↑M from Nat.one_le_cast.mpr hM]
    have hlog1d_nn : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith

    have h_rewrite : 2 * ↑n * Real.log (2 * ↑M / δ) =
        ↑n * (2 * Real.log (2 * ↑M) + 2 * Real.log (1 / δ)) := by
      rw [hlog_split]; ring
    rw [h_rewrite]
    rw [Real.sqrt_mul (le_of_lt hn_pos)]

    have h_sqrt_add : Real.sqrt (2 * Real.log (2 * ↑M) + 2 * Real.log (1 / δ)) ≤
        Real.sqrt (2 * Real.log (2 * ↑M)) + Real.sqrt (2 * Real.log (1 / δ)) := by
      rw [← Real.sqrt_sq (by positivity :
          0 ≤ Real.sqrt (2 * Real.log (2 * ↑M)) + Real.sqrt (2 * Real.log (1 / δ)))]
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.log (2 * ↑M) by positivity),
                 Real.sq_sqrt (show 0 ≤ 2 * Real.log (1 / δ) by positivity),
                 Real.sqrt_nonneg (2 * Real.log (2 * ↑M)),
                 Real.sqrt_nonneg (2 * Real.log (1 / δ))]

    have h_factor : ∀ x : ℝ,
        Real.sqrt (↑n) * Real.sqrt x = ↑n * Real.sqrt (x / ↑n) := by
      intro x
      rw [← Real.sqrt_mul (le_of_lt hn_pos)]
      rw [show ↑n * x = ↑n ^ 2 * (x / ↑n) from by field_simp]
      rw [Real.sqrt_mul (sq_nonneg _)]
      rw [Real.sqrt_sq (le_of_lt hn_pos)]
    calc 4 * (σ * (Real.sqrt ↑n * Real.sqrt (2 * Real.log (2 * ↑M) + 2 * Real.log (1 / δ))))
        ≤ 4 * (σ * (Real.sqrt ↑n *
          (Real.sqrt (2 * Real.log (2 * ↑M)) + Real.sqrt (2 * Real.log (1 / δ))))) := by
          gcongr

      _ = 4 * σ * (Real.sqrt ↑n * Real.sqrt (2 * Real.log (2 * ↑M)) +
          Real.sqrt ↑n * Real.sqrt (2 * Real.log (1 / δ))) := by ring
      _ = 4 * σ * (↑n * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
          ↑n * Real.sqrt (2 * Real.log (1 / δ) / ↑n)) := by
          rw [h_factor (2 * Real.log (2 * ↑M)), h_factor (2 * Real.log (1 / δ))]
      _ = ↑n * (4 * σ * (Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
          Real.sqrt (2 * Real.log (1 / δ) / ↑n))) := by ring

  have hConc : ∀ (v : Fin M → ℝ),
      2 * (∑ i : Fin n, ε_val i * (Φ.mulVec v) i) ≤
        ↑n * τ / 2 * l1norm_35 v := by
    intro v

    have h1 : 2 * (∑ i, ε_val i * (Φ.mulVec v) i) ≤
        2 * |∑ i, ε_val i * (Φ.mulVec v) i| := by
      nlinarith [abs_nonneg (∑ i, ε_val i * (Φ.mulVec v) i),
                 le_abs_self (∑ i, ε_val i * (Φ.mulVec v) i)]
    have h2 := hHolder v

    have h2B : 2 * B ≤ ↑n * τ / 2 := by linarith

    have hl1_nn : 0 ≤ l1norm_35 v := by
      unfold l1norm_35; apply Finset.sum_nonneg; intros; exact abs_nonneg _
    calc 2 * (∑ i, ε_val i * (Φ.mulVec v) i)
        ≤ 2 * |∑ i, ε_val i * (Φ.mulVec v) i| := h1
      _ ≤ 2 * B * l1norm_35 v := h2

      _ ≤ ↑n * τ / 2 * l1norm_35 v := by nlinarith

  have hChain := stage_A_chain_bound Φ Y f ε_val τ α k hα_pos hα_lt hk
    hτ_nonneg θhat θ' hModel hLasso hConc hINC hθ'_sparse

  exact theorem_3_5_lasso_sparse_oracle Φ Y f τ α hα_pos hα_lt θhat θ' hChain

/-- Refined concentration event: under sub-Gaussian noise with parameter `σ`
and the column-norm bound `‖Φ_{·j}‖² ≤ n`, with probability at least `1 − δ`
every column satisfies `|⟨ε, Φ_{·j}⟩| ≤ σ √(2n log(2M/δ))`. -/
theorem refined_concentration_event_no_colnorm
    {Ω : Type*} {_ : MeasurableSpace Ω}
    {n M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (σ δ : ℝ)
    (hσ : 0 < σ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hn : 0 < n) (hM : 0 < M)
    (hsubG : IsSubGaussianNoise ε σ μ)
    (hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n) :
    μ {ω | ∀ (j : Fin M),
        |∑ i : Fin n, ε ω i * Φ i j| ≤
          σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ))}
    ≥ ENNReal.ofReal (1 - δ) := by

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr hM
  have h2M_pos : (0 : ℝ) < 2 * ↑M := by positivity
  have h2Mδ_pos : (0 : ℝ) < 2 * ↑M / δ := div_pos h2M_pos hδ_pos
  have hlog2Mδ : 0 < Real.log (2 * ↑M / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ_pos]
    have : (1 : ℝ) ≤ ↑M := Nat.one_le_cast.mpr hM
    nlinarith
  set t := σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ)) with ht_def
  have ht_pos : 0 < t := by positivity

  have hbad_le : μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ≤
      ENNReal.ofReal (2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
    have hsub : {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ⊆
        ⋃ j : Fin M, {ω | |∑ i, ε ω i * Φ i j| > t} := by
      intro ω ⟨j, hj⟩; exact Set.mem_iUnion.mpr ⟨j, hj⟩
    calc μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}
        ≤ μ (⋃ j : Fin M, {ω | |∑ i, ε ω i * Φ i j| > t}) := measure_mono hsub
      _ ≤ ∑' j : Fin M, μ {ω | |∑ i, ε ω i * Φ i j| > t} := measure_iUnion_le _
      _ = ∑ j : Fin M, μ {ω | |∑ i, ε ω i * Φ i j| > t} :=
          tsum_eq_sum (fun _ h => absurd (Finset.mem_univ _) h)
      _ ≤ ∑ _j : Fin M,
          ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          apply Finset.sum_le_sum; intro j _
          exact per_column_subG_tail_bound μ ε Φ σ hσ hn hsubG hsubG_full hIndep hMeas hColNorm j t ht_pos
      _ = ↑M * ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal (2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2))) := by
          rw [← ENNReal.ofReal_natCast (n := M)]
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
          congr 1; ring

  have h_tail : 2 * ↑M * Real.exp (-t ^ 2 / (2 * ↑n * σ ^ 2)) ≤ δ := by
    have ht_sq : t ^ 2 = σ ^ 2 * (2 * ↑n * Real.log (2 * ↑M / δ)) := by
      rw [ht_def]
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * ↑n * Real.log (2 * ↑M / δ))]
    have hfact : t ^ 2 / (2 * ↑n * σ ^ 2) = Real.log (2 * ↑M / δ) := by
      rw [ht_sq]; field_simp
    have hexp_neg_rw : -t ^ 2 / (2 * ↑n * σ ^ 2) = -(t ^ 2 / (2 * ↑n * σ ^ 2)) := neg_div _ _
    rw [hexp_neg_rw, hfact]
    have hexp : Real.exp (-(Real.log (2 * ↑M / δ))) ≤ (2 * ↑M / δ)⁻¹ :=
      exp_neg_le_inv' h2Mδ_pos le_rfl
    rw [inv_div] at hexp
    calc 2 * ↑M * Real.exp (-Real.log (2 * ↑M / δ))
        ≤ 2 * ↑M * (δ / (2 * ↑M)) := by
          apply mul_le_mul_of_nonneg_left hexp (le_of_lt h2M_pos)
      _ = δ := by field_simp

  have hbad_le_delta : μ {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t} ≤
      ENNReal.ofReal δ :=
    le_trans hbad_le (ENNReal.ofReal_le_ofReal h_tail)

  have hgood_eq : {ω | ∀ (j : Fin M), |∑ i : Fin n, ε ω i * Φ i j| ≤ t} =
      {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_lt]
  rw [hgood_eq]
  set bad := {ω | ∃ j : Fin M, |∑ i, ε ω i * Φ i j| > t}
  have h_sum : 1 ≤ μ bad + μ badᶜ := by
    rw [← measure_univ (μ := μ)]
    calc μ Set.univ = μ (bad ∪ badᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ bad + μ badᶜ := measure_union_le bad badᶜ
  rw [show ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ from by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_sub _ (le_of_lt hδ_pos)]
  calc 1 - ENNReal.ofReal δ ≤ 1 - μ bad := tsub_le_tsub_left hbad_le_delta _
    _ ≤ μ badᶜ := by
        have := tsub_le_iff_left.mpr h_sum
        exact this

/-- Combined Stage-B form: convert the column event directly into the
oracle inequality with the `1024 σ² (log(eM) + log(1/δ)) · |θ'|₀ / α`
constant explicitly. -/
theorem column_event_to_combined_stageB_form
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (Y : Fin n → ℝ)
    (ε_val : Fin n → ℝ)
    (θhat θ' : Fin M → ℝ)
    (σ τ α δ : ℝ)
    (hσ : 0 < σ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (k : ℕ) (hk : 0 < k)
    (hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n))
    (hModel : ∀ i, Y i = f i + ε_val i)
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (hINC : INC_condition Φ k)
    (hLasso : lassoObjective_35 Y Φ τ θhat ≤ lassoObjective_35 Y Φ τ θ')
    (hθ'_sparse : support_size_35 θ' ≤ k)
    (hcol : ∀ j : Fin M, |∑ i : Fin n, ε_val i * Φ i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ))) :
    (1 - α) * sqNorm (f - Φ.mulVec θhat) ≤
        (1 + α) * sqNorm (f - Φ.mulVec θ') +
          1024 * σ ^ 2 * (Real.log (Real.exp 1 * ↑M) + Real.log (1 / δ)) *
            ↑(support_size_35 θ') / α := by

  have hStageB := column_event_to_stageB_split hn hM Φ f Y ε_val θhat θ' σ τ α δ
    hσ hα_pos hα_lt hδ_pos hδ_le k hk hτ hModel hColNorm hINC hLasso hθ'_sparse hcol

  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  set a := Real.sqrt (2 * Real.log (2 * ↑M) / ↑n)
  set b := Real.sqrt (2 * Real.log (1 / δ) / ↑n)
  have hτ_val : τ = 4 * σ * (a + b) := by linarith
  have hlog2M : 0 < Real.log (2 * ↑M) := by
    apply Real.log_pos; linarith [show (1 : ℝ) ≤ ↑M from Nat.one_le_cast.mpr hM]
  have hlog1d : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
  have ha_sq : a ^ 2 = 2 * Real.log (2 * ↑M) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn_pos))
  have hb_sq : b ^ 2 = 2 * Real.log (1 / δ) / ↑n :=
    Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hn_pos))
  set L := Real.log (Real.exp 1 * ↑M)
  set Ld := Real.log (1 / δ)

  have h16tau_eq : 16 * τ ^ 2 = 256 * σ ^ 2 * (a + b) ^ 2 := by rw [hτ_val]; ring
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h_expand : 512 * σ ^ 2 * (a ^ 2 + b ^ 2) =
      1024 * σ ^ 2 * (Real.log (2 * ↑M) + Ld) / ↑n := by
    rw [ha_sq, hb_sq]; field_simp; ring
  have h_log_mono : Real.log (2 * ↑M) ≤ L := by
    apply Real.log_le_log (by positivity)
    nlinarith [Real.exp_one_gt_two]
  have h16tau_bound : 16 * τ ^ 2 ≤ 1024 * σ ^ 2 * (L + Ld) / ↑n := by
    calc 16 * τ ^ 2 = 256 * σ ^ 2 * (a + b) ^ 2 := h16tau_eq
      _ ≤ 256 * σ ^ 2 * (2 * (a ^ 2 + b ^ 2)) := by nlinarith [sq_nonneg σ]
      _ = 512 * σ ^ 2 * (a ^ 2 + b ^ 2) := by ring
      _ = 1024 * σ ^ 2 * (Real.log (2 * ↑M) + Ld) / ↑n := h_expand
      _ ≤ 1024 * σ ^ 2 * (L + Ld) / ↑n := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
          nlinarith [sq_nonneg σ]
  have h16tau_n : 16 * τ ^ 2 * ↑n ≤ 1024 * σ ^ 2 * (L + Ld) := by
    have h := mul_le_mul_of_nonneg_right h16tau_bound (le_of_lt hn_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hn_pos)] at h

  set s := (↑(support_size_35 θ') : ℝ)
  have h_tail : 16 * τ ^ 2 * ↑n * s / α ≤ 1024 * σ ^ 2 * (L + Ld) * s / α := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hα_pos)
    apply mul_le_mul_of_nonneg_right h16tau_n (Nat.cast_nonneg' (support_size_35 θ'))
  linarith

/-- Stage B in separated MSE form: combines the column event, Lasso optimality,
INC, and sparsity to bound `MSE(Φθ̂, f)` by `(1+α)/(1−α) · MSE(Φθ', f)` plus
`log(eM)` and `log(1/δ)` contributions. -/
theorem stageB_separated_form
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (Y : Fin n → ℝ)
    (ε_val : Fin n → ℝ)
    (θhat θ' : Fin M → ℝ)
    (σ τ α δ : ℝ)
    (hσ : 0 < σ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (k : ℕ) (hk : 0 < k)
    (hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n))
    (hModel : ∀ i, Y i = f i + ε_val i)
    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)
    (hINC : INC_condition Φ k)
    (hLasso : lassoObjective_35 Y Φ τ θhat ≤ lassoObjective_35 Y Φ τ θ')
    (hθ'_sparse : support_size_35 θ' ≤ k)
    (hcol : ∀ j : Fin M, |∑ i : Fin n, ε_val i * Φ i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ))) :
    MSE_35 (Φ *ᵥ θhat) f ≤
        (1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ') f +
          1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
            ↑(support_size_35 θ') *
            Real.log (Real.exp 1 * ↑M) +
          1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
            ↑(support_size_35 θ') *
            Real.log (1 / δ) := by

  have hComb := column_event_to_combined_stageB_form hn hM Φ f Y ε_val θhat θ' σ τ α δ
    hσ hα_pos hα_lt hδ_pos hδ_le k hk hτ hModel hColNorm hINC hLasso hθ'_sparse hcol

  have hStageB := column_event_to_stageB_split hn hM Φ f Y ε_val θhat θ' σ τ α δ
    hσ hα_pos hα_lt hδ_pos hδ_le k hk hτ hModel hColNorm hINC hLasso hθ'_sparse hcol
  exact tau_to_mse_conversion hn hM Φ f θhat θ' σ τ α δ hσ hα_pos hα_lt hδ_pos hδ_le hτ hStageB

/-- Theorem 3.5 (Lasso oracle inequality, High-Dimensional Statistics, Ch. 3):
for the general regression model `Y = f + ε` with `ε ~ subGₙ(σ²)` and `Φ`
satisfying `INC(k)`, the Lasso estimator `θ̂^L` with
`2τ = 8σ √(2 log(2M)/n) + 8σ √(2 log(1/δ)/n)` satisfies
`MSE(φ_{θ̂^L}) ≤ inf_{k-sparse θ} { (1+α)/(1−α) · MSE(φ_θ) + Cσ²/(α(1−α)n) · |θ|₀ log(eM) } + Cσ²/(α(1−α)n) · log(1/δ)`
with probability at least `1 − δ`. -/
theorem thm_3_5_lasso_oracle_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)

    (ε : Ω → Fin n → ℝ)
    (Y : Ω → Fin n → ℝ)

    (hModel : ∀ ω i, Y ω i = f i + ε ω i)

    (θhat : Ω → Fin M → ℝ)

    (σ : ℝ) (hσ : 0 < σ)
    (k : ℕ) (hk : 0 < k)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hsubG : IsSubGaussianNoise ε σ μ)

    (hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeas : ∀ i : Fin n, Measurable (fun ω => ε ω i))

    (hINC : INC_condition Φ k)

    (hColNorm : ∀ j : Fin M, ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n)

    (τ : ℝ)
    (hτ : 2 * τ = 8 * σ * Real.sqrt (2 * Real.log (2 * ↑M) / ↑n) +
                    8 * σ * Real.sqrt (2 * Real.log (1 / δ) / ↑n))

    (hLasso : ∀ ω θ, lassoObjective_35 (Y ω) Φ τ (θhat ω) ≤
                      lassoObjective_35 (Y ω) Φ τ θ) :
    ∃ (C_const : ℝ), 0 < C_const ∧
    μ {ω | MSE_35 (Φ *ᵥ (θhat ω)) f ≤
      (⨅ θ : {θ : Fin M → ℝ // support_size_35 θ ≤ k},
        ((1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ.1) f +
        C_const * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(support_size_35 θ.1) *
          Real.log (Real.exp 1 * ↑M))) +
      C_const * σ ^ 2 / (α * (1 - α) * ↑n) * Real.log (1 / δ)}
    ≥ ENNReal.ofReal (1 - δ) := by

  refine ⟨1024 * ↑k, by positivity, ?_⟩

  haveI hNE : Nonempty {θ : Fin M → ℝ // support_size_35 θ ≤ k} := by
    exact ⟨⟨0, by simp [support_size_35]⟩⟩

  set E : Set Ω := {ω | ∀ (j : Fin M),
      |∑ i : Fin n, ε ω i * Φ i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑M / δ))} with hE_def

  suffices hE_prob : μ E ≥ ENNReal.ofReal (1 - δ) by
    apply le_trans hE_prob
    apply measure_mono

    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢

    set Ld := Real.log (1 / δ)
    set L := Real.log (Real.exp 1 * ↑M)
    set c0 := 1024 * σ ^ 2 / (α * (1 - α) * ↑n)

    have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk
    have hk_ge_one : (1 : ℝ) ≤ ↑k := by exact_mod_cast hk
    have hSubtracted : ∀ θ' : {θ : Fin M → ℝ // support_size_35 θ ≤ k},
        MSE_35 (Φ *ᵥ (θhat ω)) f - c0 * ↑k * Ld ≤
          (1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ'.1) f +
          c0 * ↑k * ↑(support_size_35 θ'.1) * L := by
      intro ⟨θ', hθ'_sparse⟩

      have hSep := stageB_separated_form hn hM Φ f (Y ω) (ε ω)
        (θhat ω) θ' σ τ α δ hσ hα_pos hα_lt hδ_pos hδ_le k hk hτ
        (hModel ω) hColNorm hINC (hLasso ω θ') hθ'_sparse hω

      set s := (↑(support_size_35 θ') : ℝ)
      have hs_le_k : s ≤ ↑k := Nat.cast_le.mpr hθ'_sparse
      have hLd_nn : 0 ≤ Ld := by
        apply Real.log_nonneg; rw [le_div_iff₀ hδ_pos]; linarith
      have h1mα : 0 < 1 - α := by linarith
      have hc0_nn : 0 ≤ c0 := by positivity
      have hs_nn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      have hL_nn : 0 ≤ L := by
        apply Real.log_nonneg
        have hM_ge : (1 : ℝ) ≤ ↑M := Nat.one_le_cast.mpr hM
        have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 1)
        nlinarith [mul_le_mul hexp hM_ge (by linarith : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ Real.exp 1)]

      have h1 : c0 * s * Ld ≤ c0 * ↑k * Ld := by
        apply mul_le_mul_of_nonneg_right _ hLd_nn
        exact mul_le_mul_of_nonneg_left hs_le_k hc0_nn

      have h2 : c0 * s * L ≤ c0 * ↑k * s * L := by
        have : c0 * s * L = c0 * (1 * s) * L := by ring_nf
        have : c0 * ↑k * s * L = c0 * (↑k * s) * L := by ring_nf
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_ge_one hc0_nn) (mul_nonneg hs_nn hL_nn)]
      linarith

    have hInf : MSE_35 (Φ *ᵥ (θhat ω)) f - c0 * ↑k * Ld ≤
        ⨅ θ : {θ : Fin M → ℝ // support_size_35 θ ≤ k},
          ((1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ.1) f +
          c0 * ↑k * ↑(support_size_35 θ.1) * L) :=
      le_ciInf hSubtracted

    have hc0_eq : c0 = 1024 * σ ^ 2 / (α * (1 - α) * ↑n) := rfl

    suffices h : MSE_35 (Φ *ᵥ (θhat ω)) f ≤
        (⨅ θ : {θ : Fin M → ℝ // support_size_35 θ ≤ k},
          ((1 + α) / (1 - α) * MSE_35 (Φ *ᵥ θ.1) f +
          c0 * ↑k * ↑(support_size_35 θ.1) * L)) +
        c0 * ↑k * Ld from by
      convert h using 2
      · congr 1
        congr 1
        funext θ
        ring
      · ring
    linarith

  exact refined_concentration_event_no_colnorm μ ε Φ σ δ hσ hδ_pos hδ_le hn hM hsubG hsubG_full hIndep hMeas hColNorm

end Rigollet.Chapter3
