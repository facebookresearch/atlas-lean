/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Filter Topology

noncomputable section

/-- Monotonicity of expectations along a submartingale: if `X` is a submartingale and `i ≤ j`,
then `∫ X_i dμ ≤ ∫ X_j dμ`. -/
lemma submartingale_integral_mono
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hsub : Submartingale X ℱ μ) {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, X i ω ∂μ ≤ ∫ ω, X j ω ∂μ := by
  have h_ae := hsub.2.1 i j hij
  calc ∫ ω, X i ω ∂μ
      ≤ ∫ ω, μ[X j | ↑(ℱ i)] ω ∂μ :=
        integral_mono_ae (hsub.2.2 i) integrable_condExp h_ae
    _ = ∫ ω, X j ω ∂μ := integral_condExp (ℱ.le i) (μ := μ)

/-- `L¹`-bound for a submartingale `X` from a uniform bound on the positive parts: if
`∫ (X n)⁺ dμ ≤ C` for every `n`, then `∫ ‖X n‖ dμ ≤ 2C - ∫ X 0 dμ`. This uses the
identity `‖x‖ = 2 x⁺ - x` together with monotonicity of `∫ X n dμ`. -/
lemma submartingale_integral_norm_le
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hsub : Submartingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) (n : ℕ) :
    ∫ ω, ‖X n ω‖ ∂μ ≤ 2 * C - ∫ ω, X 0 ω ∂μ := by
  have hint := hsub.2.2
  have hmax : Integrable (fun ω => (X n ω)⁺) μ := (hint n).sup (integrable_zero _ _ μ)

  have key : ∫ ω, ‖X n ω‖ ∂μ = 2 * ∫ ω, (X n ω)⁺ ∂μ - ∫ ω, X n ω ∂μ := by
    have kk : ∀ ω, ‖X n ω‖ = 2 * (X n ω)⁺ - X n ω := by
      intro ω
      simp only [Real.norm_eq_abs, posPart]
      rcases le_or_gt (X n ω) 0 with h | h
      · simp [abs_of_nonpos h, max_eq_right h]
      · simp [abs_of_pos h, max_eq_left h.le]; ring
    simp_rw [kk]
    rw [integral_sub (hmax.const_mul 2) (hint n)]
    congr 1; exact integral_const_mul 2 _

  have hmono : ∫ ω, X 0 ω ∂μ ≤ ∫ ω, X n ω ∂μ :=
    submartingale_integral_mono hsub (Nat.zero_le n)
  linarith [hbdd n]

/-- **Submartingale almost-sure convergence theorem.** If `X` is a submartingale on a
probability space with `∫ (X n)⁺ dμ` uniformly bounded by some `C`, then there exists an
integrable limit `X_∞` such that `X n → X_∞` almost surely. -/
theorem submartingale_ae_convergence
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {C : ℝ}
    (hsub : Submartingale X ℱ μ)
    (hbdd : ∀ n, ∫ ω, (X n ω)⁺ ∂μ ≤ C) :
    ∃ X_inf : Ω → ℝ, Integrable X_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_inf ω)) := by
  have hint : ∀ n, Integrable (X n) μ := hsub.2.2


  have h_norm_bdd := submartingale_integral_norm_le hsub hbdd
  set B := (2 * C - ∫ ω, X 0 ω ∂μ).toNNReal
  have h_eLpNorm : ∀ n, eLpNorm (X n) 1 μ ≤ ↑B := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    rw [ENNReal.ofReal_le_coe]
    exact le_trans (h_norm_bdd n) (Real.le_coe_toNNReal _)


  have hconv := hsub.ae_tendsto_limitProcess h_eLpNorm

  have hasm : ∀ n, AEStronglyMeasurable (X n) μ :=
    fun n => (hsub.1 n).aestronglyMeasurable.mono (ℱ.le n)
  have hint_lim : Integrable (ℱ.limitProcess X μ) μ :=
    memLp_one_iff_integrable.mp (Filtration.memLp_limitProcess_of_eLpNorm_bdd hasm h_eLpNorm)
  exact ⟨ℱ.limitProcess X μ, hint_lim, hconv⟩
