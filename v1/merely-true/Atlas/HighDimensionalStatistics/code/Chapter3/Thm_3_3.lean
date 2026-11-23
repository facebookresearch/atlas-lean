/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option maxHeartbeats 4800000

open Matrix MeasureTheory

namespace Rigollet.Chapter3

/-- Expansion of `⟨a + b, a + b⟩ = ⟨a, a⟩ + 2 ⟨a, b⟩ + ⟨b, b⟩`. -/
lemma dotProduct_add_expand {n : ℕ} (a b : Fin n → ℝ) :
    dotProduct (a + b) (a + b) =
    dotProduct a a + 2 * dotProduct a b + dotProduct b b := by
  simp only [dotProduct_add, add_dotProduct, dotProduct_comm b a]; ring

/-- Pythagorean identity for orthogonal vectors in `Fin n → ℝ`:
if `⟨a, b⟩ = 0`, then `⟨a + b, a + b⟩ = ⟨a, a⟩ + ⟨b, b⟩`. -/
lemma pythagoras_dotProduct {n : ℕ} (a b : Fin n → ℝ)
    (h : dotProduct a b = 0) :
    dotProduct (a + b) (a + b) = dotProduct a a + dotProduct b b := by
  rw [dotProduct_add_expand]; linarith

/-- Basic inequality for Theorem 3.3: from the least-squares optimality of
`θ̂` one obtains, for any reference `θbar`,
`‖f - Φ θ̂‖² ≤ ‖f - Φ θbar‖² + 2 ⟨ε, Φ θ̂ - Φ θbar⟩`. -/
theorem thm_3_3_basic_inequality
    {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f ε : Fin n → ℝ) (θhat θbar : Fin M → ℝ)
    (hLS : ∀ θ, dotProduct (f + ε - Φ *ᵥ θhat) (f + ε - Φ *ᵥ θhat) ≤
               dotProduct (f + ε - Φ *ᵥ θ) (f + ε - Φ *ᵥ θ)) :
    dotProduct (f - Φ *ᵥ θhat) (f - Φ *ᵥ θhat) ≤
      dotProduct (f - Φ *ᵥ θbar) (f - Φ *ᵥ θbar) +
      2 * dotProduct ε (Φ *ᵥ θhat - Φ *ᵥ θbar) := by
  have h1 := hLS θbar
  have hrhat : f + ε - Φ *ᵥ θhat = (f - Φ *ᵥ θhat) + ε := by ext i; simp; ring
  have hrbar : f + ε - Φ *ᵥ θbar = (f - Φ *ᵥ θbar) + ε := by ext i; simp; ring
  rw [hrhat, hrbar, dotProduct_add_expand, dotProduct_add_expand] at h1
  have key : dotProduct (f - Φ *ᵥ θbar) ε - dotProduct (f - Φ *ᵥ θhat) ε =
    dotProduct ε (Φ *ᵥ θhat - Φ *ᵥ θbar) := by
    simp only [dotProduct_sub, dotProduct_comm]; ring
  linarith

/-- Pythagorean step in the proof of Theorem 3.3: when `Φ θbar` is the
projection of `f` (so `⟨f - Φ θbar, Φ v⟩ = 0` for every `v`), one gets
`‖Φ θ̂ - Φ θbar‖² ≤ 2 ⟨ε, Φ θ̂ - Φ θbar⟩`. -/
theorem thm_3_3_pythagorean_step
    {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f ε : Fin n → ℝ) (θhat θbar : Fin M → ℝ)
    (hLS : ∀ θ, dotProduct (f + ε - Φ *ᵥ θhat) (f + ε - Φ *ᵥ θhat) ≤
               dotProduct (f + ε - Φ *ᵥ θ) (f + ε - Φ *ᵥ θ))
    (hProj : ∀ v : Fin M → ℝ, dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ v) = 0) :
    dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) ≤
      2 * dotProduct ε (Φ *ᵥ θhat - Φ *ᵥ θbar) := by
  have hbasic := thm_3_3_basic_inequality Φ f ε θhat θbar hLS
  have hdecomp : f - Φ *ᵥ θhat = (f - Φ *ᵥ θbar) + (Φ *ᵥ θbar - Φ *ᵥ θhat) := by
    ext i; simp
  have horth : dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ θbar - Φ *ᵥ θhat) = 0 := by
    rw [show Φ *ᵥ θbar - Φ *ᵥ θhat = Φ *ᵥ (θbar - θhat) from by simp [mulVec_sub]]
    exact hProj _
  rw [hdecomp, pythagoras_dotProduct _ _ horth] at hbasic
  have hsymm : dotProduct (Φ *ᵥ θbar - Φ *ᵥ θhat) (Φ *ᵥ θbar - Φ *ᵥ θhat) =
    dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) := by
    rw [show Φ *ᵥ θbar - Φ *ᵥ θhat = -(Φ *ᵥ θhat - Φ *ᵥ θbar) from by ext i; simp]
    rw [dotProduct_neg, neg_dotProduct, neg_neg]
  linarith

/-- Empirical mean squared error: `MSE'(fhat, f) = (1/n) ∑ᵢ (fhatᵢ - fᵢ)²`. -/
noncomputable def MSE' {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- Reformulation of `MSE'` in terms of the dot product:
`MSE'(v, f) = (1/n) · ⟨v - f, v - f⟩`. -/
lemma MSE'_eq_dotProduct {n : ℕ} (v f : Fin n → ℝ) :
    MSE' v f = (1 / (n : ℝ)) * dotProduct (v - f) (v - f) := by
  unfold MSE' dotProduct; congr 1; apply Finset.sum_congr rfl
  intro i _; simp [Pi.sub_apply]; ring

/-- The squared-norm dot product is symmetric in its sign:
`⟨v - f, v - f⟩ = ⟨f - v, f - v⟩`. -/
lemma dotProduct_sub_comm' {n : ℕ} (v f : Fin n → ℝ) :
    dotProduct (v - f) (v - f) = dotProduct (f - v) (f - v) := by
  rw [show v - f = -(f - v) from by ext i; simp]
  rw [dotProduct_neg, neg_dotProduct, neg_neg]

/-- The dot product of a real vector with itself is non-negative. -/
lemma dotProduct_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ dotProduct v v := by
  unfold dotProduct
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (v i)

/-- Pointwise comparison underlying the oracle inequality of Theorem 3.3:
for the projection `Φ θbar` of `f`, and any candidate `θ`,
`‖f - Φ θ̂‖² ≤ ‖f - Φ θ‖² + ‖Φ θ̂ - Φ θbar‖²`. -/
lemma pointwise_bound {n M : ℕ} (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ) (θhat θbar : Fin M → ℝ)
    (hProj : ∀ v : Fin M → ℝ, dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ v) = 0) :
    ∀ θ : Fin M → ℝ,
      dotProduct (f - Φ *ᵥ θhat) (f - Φ *ᵥ θhat) ≤
        dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) +
        dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) := by
  intro θ
  have hdecomp_hat : f - Φ *ᵥ θhat = (f - Φ *ᵥ θbar) + (Φ *ᵥ θbar - Φ *ᵥ θhat) := by
    ext i; simp
  have horth_hat : dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ θbar - Φ *ᵥ θhat) = 0 := by
    rw [show Φ *ᵥ θbar - Φ *ᵥ θhat = Φ *ᵥ (θbar - θhat) from by simp [mulVec_sub]]
    exact hProj _
  rw [hdecomp_hat, pythagoras_dotProduct _ _ horth_hat]
  have hsymm : dotProduct (Φ *ᵥ θbar - Φ *ᵥ θhat) (Φ *ᵥ θbar - Φ *ᵥ θhat) =
    dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) :=
    dotProduct_sub_comm' _ _
  rw [hsymm]
  have hdecomp_theta : f - Φ *ᵥ θ = (f - Φ *ᵥ θbar) + (Φ *ᵥ θbar - Φ *ᵥ θ) := by
    ext i; simp
  have horth_theta : dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ θbar - Φ *ᵥ θ) = 0 := by
    rw [show Φ *ᵥ θbar - Φ *ᵥ θ = Φ *ᵥ (θbar - θ) from by simp [mulVec_sub]]
    exact hProj _
  rw [hdecomp_theta, pythagoras_dotProduct _ _ horth_theta]
  linarith [dotProduct_self_nonneg' (Φ *ᵥ θbar - Φ *ᵥ θ)]

/-- Pointwise oracle inequality (deterministic version): given a high-prob
control `‖Φ θ̂ - Φ θbar‖² ≤ R` for some `R`, then for every `θ`,
`MSE'(Φ θ̂, f) ≤ MSE'(Φ θ, f) + R/n`. -/
theorem thm_3_3_oracle_inequality_pointwise
    {n M : ℕ} (hn : (0 : ℝ) < n) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ) (θhat θbar : Fin M → ℝ) (R : ℝ)
    (hProj : ∀ v : Fin M → ℝ, dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ v) = 0)
    (hConc : dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) ≤ R) :
    ∀ θ : Fin M → ℝ,
      MSE' (Φ *ᵥ θhat) f ≤ MSE' (Φ *ᵥ θ) f + (1 / (n : ℝ)) * R := by
  intro θ
  rw [MSE'_eq_dotProduct, MSE'_eq_dotProduct]
  have hpw := pointwise_bound Φ f θhat θbar hProj θ
  have hn_inv_pos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc 1 / (↑n) * dotProduct (Φ *ᵥ θhat - f) (Φ *ᵥ θhat - f)
      = 1 / (↑n) * dotProduct (f - Φ *ᵥ θhat) (f - Φ *ᵥ θhat) := by
        congr 1; exact dotProduct_sub_comm' _ _
    _ ≤ 1 / (↑n) * (dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) +
        dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar)) := by
        apply mul_le_mul_of_nonneg_left hpw hn_inv_pos
    _ ≤ 1 / (↑n) * dotProduct (f - Φ *ᵥ θ) (f - Φ *ᵥ θ) + 1 / (↑n) * R := by
        rw [mul_add]
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left hConc hn_inv_pos
    _ = 1 / (↑n) * dotProduct (Φ *ᵥ θ - f) (Φ *ᵥ θ - f) + 1 / (↑n) * R := by
        congr 1; congr 1; exact (dotProduct_sub_comm' _ _).symm

/-- Deterministic infimum form of the oracle inequality:
`MSE'(Φ θ̂, f) ≤ inf_θ MSE'(Φ θ, f) + R/n`. -/
theorem thm_3_3_oracle_inequality_det
    {n M : ℕ} (hn : (0 : ℝ) < n) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ) (θhat θbar : Fin M → ℝ) (R : ℝ)
    (hProj : ∀ v : Fin M → ℝ, dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ v) = 0)
    (hConc : dotProduct (Φ *ᵥ θhat - Φ *ᵥ θbar) (Φ *ᵥ θhat - Φ *ᵥ θbar) ≤ R) :
    MSE' (Φ *ᵥ θhat) f ≤
      (⨅ θ : Fin M → ℝ, MSE' (Φ *ᵥ θ) f) + (1 / (n : ℝ)) * R := by
  have hpw := thm_3_3_oracle_inequality_pointwise hn Φ f θhat θbar R hProj hConc
  have hsub : ∀ θ : Fin M → ℝ, MSE' (Φ *ᵥ θhat) f - 1 / (↑n) * R ≤ MSE' (Φ *ᵥ θ) f :=
    fun θ => by linarith [hpw θ]
  haveI : Nonempty (Fin M → ℝ) := ⟨fun _ => 0⟩
  have := le_ciInf hsub
  linarith

end Rigollet.Chapter3

namespace Rigollet.Chapter3

open Matrix MeasureTheory

/-- Theorem 3.3 (least squares oracle inequality): for the least squares
estimator under the sub-Gaussian noise model `Y = f + ε`, `ε ~ subG_n(σ²)`,
with probability at least `1 - δ`,
`MSE(φ_{θ̂^LS}) ≤ inf_θ MSE(φ_θ) + C σ² M log(1/δ) / n`. -/
theorem thm_3_3
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n M : ℕ} (hn : (0 : ℝ) < n) (hM : 0 < M)
    (Φ : Matrix (Fin n) (Fin M) ℝ)
    (f : Fin n → ℝ)
    (ε : Ω → Fin n → ℝ)
    (θhat : Ω → Fin M → ℝ)
    (θbar : Fin M → ℝ)
    (hProj : ∀ v : Fin M → ℝ, dotProduct (f - Φ *ᵥ θbar) (Φ *ᵥ v) = 0)
    (hLS : ∀ ω, ∀ θ,
      dotProduct (f + ε ω - Φ *ᵥ (θhat ω)) (f + ε ω - Φ *ᵥ (θhat ω)) ≤
      dotProduct (f + ε ω - Φ *ᵥ θ) (f + ε ω - Φ *ᵥ θ))
    (σ : ℝ) (hσ : 0 < σ)
    (hsubG : ∀ (v : Fin n → ℝ),
      dotProduct v v ≤ 1 →
      ∀ s : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (s * dotProduct (ε ω) v)) ∂μ ≤
        ENNReal.ofReal (Real.exp (s ^ 2 * σ ^ 2 / 2)))
    (hε_meas : ∀ j, Measurable (fun ω => ε ω j))
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hδ_small : δ ≤ Real.exp (-1)) :

    (∀ ω, ∀ θ' : Fin M → ℝ,
      dotProduct (f - Φ *ᵥ (θhat ω)) (f - Φ *ᵥ (θhat ω)) ≤
        dotProduct (f - Φ *ᵥ θ') (f - Φ *ᵥ θ') +
        2 * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θ')) ∧

    (∀ ω, dotProduct (Φ *ᵥ (θhat ω) - Φ *ᵥ θbar) (Φ *ᵥ (θhat ω) - Φ *ᵥ θbar) ≤
      2 * dotProduct (ε ω) (Φ *ᵥ (θhat ω) - Φ *ᵥ θbar)) ∧

    (∃ C : ℝ, 0 < C ∧ ∀ θ : Fin M → ℝ,
      μ {ω | MSE' (Φ *ᵥ (θhat ω)) f ≤
        MSE' (Φ *ᵥ θ) f +
        C * σ ^ 2 * ↑M * Real.log (1 / δ) / ↑n} ≥
      ENNReal.ofReal (1 - δ)) := by
  refine ⟨?_, ?_, ?_⟩

  · intro ω θ'
    exact thm_3_3_basic_inequality Φ f (ε ω) (θhat ω) θ' (hLS ω)

  · intro ω
    exact thm_3_3_pythagorean_step Φ f (ε ω) (θhat ω) θbar (hLS ω) hProj

  ·
    have mulVec_sub_comm : ∀ (a b : Fin M → ℝ),
        Φ *ᵥ a - Φ *ᵥ b = Φ *ᵥ (a - b) := fun a b => by
      rw [show Φ *ᵥ (a - b) = Φ *ᵥ a - Φ *ᵥ b from by simp [mulVec_sub]]

    have hfund : ∀ ω, dotProduct (Φ *ᵥ (θhat ω - θbar)) (Φ *ᵥ (θhat ω - θbar)) ≤
        2 * dotProduct (ε ω) (Φ *ᵥ (θhat ω - θbar)) := by
      intro ω
      have h := thm_3_3_pythagorean_step Φ f (ε ω) (θhat ω) θbar (hLS ω) hProj
      rw [mulVec_sub_comm] at h
      exact h

    set r := (Φ.transpose * Φ).rank
    have hConc := Rigollet.Chapter2.subG_squared_norm_high_prob_bound Φ θbar ε θhat σ hσ r rfl
      δ hδ_pos hδ_le hfund hsubG hε_meas

    have hr_le_M : (r : ℝ) ≤ (M : ℝ) := by
      have h := Matrix.rank_le_card_width (Φ.transpose * Φ)
      simp only [Fintype.card_fin] at h
      exact_mod_cast h
    have hlog_pos : (1 : ℝ) ≤ Real.log (1 / δ) := by

      have hexp_le : Real.exp 1 ≤ 1 / δ := by
        rw [one_div, show Real.exp 1 = (Real.exp (-1))⁻¹ from by rw [Real.exp_neg, inv_inv]]
        exact inv_anti₀ hδ_pos hδ_small
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (1 / δ) := Real.log_le_log (Real.exp_pos 1) hexp_le
    have hM_pos_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hlog_pos' : (0 : ℝ) < Real.log (1 / δ) := lt_of_lt_of_le zero_lt_one hlog_pos

    have hbound : (↑r + Real.log (1 / δ)) ≤ 2 * ↑M * Real.log (1 / δ) := by
      have h1 : (↑r : ℝ) ≤ ↑M * Real.log (1 / δ) := by
        calc (↑r : ℝ) ≤ ↑M := hr_le_M
          _ = ↑M * 1 := (mul_one _).symm
          _ ≤ ↑M * Real.log (1 / δ) := by
            apply mul_le_mul_of_nonneg_left hlog_pos (le_of_lt hM_pos_real)
      have h2 : Real.log (1 / δ) ≤ ↑M * Real.log (1 / δ) := by
        calc Real.log (1 / δ) = 1 * Real.log (1 / δ) := (one_mul _).symm
          _ ≤ ↑M * Real.log (1 / δ) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog_pos')
            exact_mod_cast hM
      linarith

    use 128
    refine ⟨by positivity, fun θ => ?_⟩

    have hConc' : μ {ω | (Φ *ᵥ θhat ω - Φ *ᵥ θbar) ⬝ᵥ (Φ *ᵥ θhat ω - Φ *ᵥ θbar) ≤
        128 * σ ^ 2 * ↑M * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ) := by
      have hsubset : {ω | (Φ *ᵥ (θhat ω - θbar)) ⬝ᵥ (Φ *ᵥ (θhat ω - θbar)) ≤
          64 * σ ^ 2 * (↑r + Real.log (1 / δ))} ⊆
          {ω | (Φ *ᵥ θhat ω - Φ *ᵥ θbar) ⬝ᵥ (Φ *ᵥ θhat ω - Φ *ᵥ θbar) ≤
          128 * σ ^ 2 * ↑M * Real.log (1 / δ)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq, mulVec_sub_comm] at hω ⊢
        calc (Φ *ᵥ (θhat ω - θbar)) ⬝ᵥ (Φ *ᵥ (θhat ω - θbar))
            ≤ 64 * σ ^ 2 * (↑r + Real.log (1 / δ)) := hω
          _ ≤ 64 * σ ^ 2 * (2 * ↑M * Real.log (1 / δ)) := by
            apply mul_le_mul_of_nonneg_left hbound; positivity
          _ = 128 * σ ^ 2 * ↑M * Real.log (1 / δ) := by ring
      exact le_trans hConc (measure_mono hsubset)

    apply le_trans hConc'
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hdet := thm_3_3_oracle_inequality_pointwise hn Φ f (θhat ω) θbar
      (128 * σ ^ 2 * ↑M * Real.log (1 / δ)) hProj hω θ
    have hrewrite : 1 / (↑n : ℝ) * (128 * σ ^ 2 * ↑M * Real.log (1 / δ)) =
      128 * σ ^ 2 * ↑M * Real.log (1 / δ) / ↑n := by ring
    linarith

end Rigollet.Chapter3
