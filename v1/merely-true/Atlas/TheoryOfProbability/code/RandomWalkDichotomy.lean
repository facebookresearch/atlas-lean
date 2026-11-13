/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ProbabilityTheory Filter Finset Topology

noncomputable section

/-- The `n`-th partial sum `Sₙ(ω) = ∑_{i < n} Xᵢ(ω)` of the sequence of random variables `X`,
viewed as a random walk on `ℝ`. -/
def randomWalkPartialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

section RandomWalkDichotomy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (X : ℕ → Ω → ℝ)

/-- The random walk *drifts to `+∞`*: almost surely `Sₙ → +∞` as `n → ∞`. -/
def DriftsToTop : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop atTop

/-- The random walk *drifts to `-∞`*: almost surely `Sₙ → -∞` as `n → ∞`. -/
def DriftsToBot : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop atBot

/-- The random walk *oscillates*: almost surely `limsup Sₙ = +∞` and `liminf Sₙ = -∞`. -/
def Oscillates : Prop :=
  ∀ᵐ ω ∂μ, limsup (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊤ ∧
             liminf (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊥

/-- The random walk *converges to a finite limit*: almost surely there exists `l ∈ ℝ`
with `Sₙ → l`. In the i.i.d. dichotomy this corresponds to the degenerate case where
each `Xᵢ = 0`. -/
def ConvergesFinite : Prop :=
  ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop (𝓝 l)

end RandomWalkDichotomy

/-- Combinatorial lemma: if four events `E₁, E₂, E₃, E₄` cover the probability space modulo
a null set, and each has probability either `0` or `1`, then at least one of them has
probability `1`. This is the core dichotomy-selection step in the random-walk dichotomy proof. -/
theorem exists_prob_one_of_cover {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {E₁ E₂ E₃ E₄ : Set Ω}
    (h_cover : μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄)ᶜ = 0)
    (h1 : μ E₁ = 0 ∨ μ E₁ = 1)
    (h2 : μ E₂ = 0 ∨ μ E₂ = 1)
    (h3 : μ E₃ = 0 ∨ μ E₃ = 1)
    (h4 : μ E₄ = 0 ∨ μ E₄ = 1) :
    μ E₁ = 1 ∨ μ E₂ = 1 ∨ μ E₃ = 1 ∨ μ E₄ = 1 := by
  by_contra h_none
  simp only [not_or] at h_none
  obtain ⟨hne1, hne2, hne3, hne4⟩ := h_none
  have he1 : μ E₁ = 0 := h1.resolve_right hne1
  have he2 : μ E₂ = 0 := h2.resolve_right hne2
  have he3 : μ E₃ = 0 := h3.resolve_right hne3
  have he4 : μ E₄ = 0 := h4.resolve_right hne4
  have h_union : μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) = 0 := by
    have h12 : μ (E₁ ∪ E₂) = 0 :=
      nonpos_iff_eq_zero.mp (le_trans (measure_union_le E₁ E₂) (by simp [he1, he2]))
    have h123 : μ (E₁ ∪ E₂ ∪ E₃) = 0 :=
      nonpos_iff_eq_zero.mp (le_trans (measure_union_le _ E₃) (by simp [h12, he3]))
    exact nonpos_iff_eq_zero.mp (le_trans (measure_union_le _ E₄) (by simp [h123, he4]))
  have h_le := measure_univ_le_add_compl (μ := μ) (E₁ ∪ E₂ ∪ E₃ ∪ E₄)
  rw [h_union, h_cover, add_zero, measure_univ] at h_le
  exact absurd h_le (by norm_num)
