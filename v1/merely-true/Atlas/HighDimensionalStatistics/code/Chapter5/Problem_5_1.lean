/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Real

noncomputable section

/-- Problem 5.1(a): the Gaussian KL surrogate `‖θ - θ'‖² / (2σ²)` is
nonnegative. -/
theorem problem_5_1a (d : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (θ θ' : EuclideanSpace ℝ (Fin d)) :
    ‖θ - θ'‖ ^ 2 / (2 * σ ^ 2) ≥ 0 := by
  positivity

/-- KL divergence between two Bernoulli laws with parameters `p` and `q`:
`p log(p/q) + (1 - p) log((1 - p)/(1 - q))`. -/
def klBernoulli (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Strict positivity of the Bernoulli KL divergence for distinct parameters
in `(0, 1)`. -/
lemma klBernoulli_pos (θ θ' : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hθ' : 0 < θ') (hθ'1 : θ' < 1) (hne : θ ≠ θ') : 0 < klBernoulli θ θ' := by
  unfold klBernoulli
  have hθ_ne : (θ : ℝ) ≠ 0 := ne_of_gt hθ
  have hθ'_ne : (θ' : ℝ) ≠ 0 := ne_of_gt hθ'
  have h1mθ : 0 < 1 - θ := sub_pos.mpr hθ1
  have h1mθ' : 0 < 1 - θ' := sub_pos.mpr hθ'1
  have h1mθ_ne : (1 - θ : ℝ) ≠ 0 := ne_of_gt h1mθ
  have h1mθ'_ne : (1 - θ' : ℝ) ≠ 0 := ne_of_gt h1mθ'
  have hrat1 : θ' / θ ≠ 1 := by
    intro h; apply hne; linarith [div_eq_one_iff_eq hθ_ne |>.mp h]
  have hlog1 : log (θ' / θ) < θ' / θ - 1 := log_lt_sub_one_of_pos (div_pos hθ' hθ) hrat1
  have hlog2 : log ((1 - θ') / (1 - θ)) ≤ (1 - θ') / (1 - θ) - 1 :=
    log_le_sub_one_of_pos (div_pos h1mθ' h1mθ)
  have h1 : θ * log (θ' / θ) < θ' - θ := by
    calc θ * log (θ' / θ) < θ * (θ' / θ - 1) := mul_lt_mul_of_pos_left hlog1 hθ
      _ = θ' - θ := by field_simp
  have h2 : (1 - θ) * log ((1 - θ') / (1 - θ)) ≤ θ - θ' := by
    calc (1 - θ) * log ((1 - θ') / (1 - θ)) ≤ (1 - θ) * ((1 - θ') / (1 - θ) - 1) :=
          mul_le_mul_of_nonneg_left hlog2 (le_of_lt h1mθ)
      _ = θ - θ' := by field_simp; ring
  rw [show log (θ / θ') = -log (θ' / θ) from by
    rw [log_div hθ_ne hθ'_ne, log_div hθ'_ne hθ_ne]; ring]
  rw [show log ((1 - θ) / (1 - θ')) = -log ((1 - θ') / (1 - θ)) from by
    rw [log_div h1mθ_ne h1mθ'_ne, log_div h1mθ'_ne h1mθ_ne]; ring]
  nlinarith

/-- Problem 5.1(b): the Bernoulli KL is bounded below by `C·(θ - θ')²` for some
positive constant `C` depending on the pair `(θ, θ')`. -/
theorem problem_5_1b (θ θ' : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (hθ' : 0 < θ') (hθ'1 : θ' < 1) :
    ∃ C : ℝ, 0 < C ∧ C * (θ - θ') ^ 2 ≤ klBernoulli θ θ' := by
  by_cases heq : θ = θ'
  · subst heq
    exact ⟨1, one_pos, by unfold klBernoulli; simp⟩
  · have hkl := klBernoulli_pos θ θ' hθ hθ1 hθ' hθ'1 heq
    have hsq : 0 < (θ - θ') ^ 2 := by
      have : θ - θ' ≠ 0 := sub_ne_zero.mpr heq
      positivity
    refine ⟨klBernoulli θ θ' / (θ - θ') ^ 2, div_pos hkl hsq, ?_⟩
    rw [div_mul_cancel₀]
    exact ne_of_gt hsq

end
