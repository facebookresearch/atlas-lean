/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.StrongLaw

set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace StrongLaw

/-- **Strong law of large numbers** (Lecture 6): if `X 0, X 1, …` are pairwise independent,
identically distributed, integrable real-valued random variables, then the empirical means
`A_n = n⁻¹ ∑_{i < n} X i` converge `μ`-almost surely to the common expectation `∫ X 0 dμ`. -/
theorem strong_law_of_large_numbers_real
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / (n : ℝ))
      atTop (𝓝 (∫ x, X 0 x ∂μ)) := by
  have h := ProbabilityTheory.strong_law_ae X hint hindep hident
  filter_upwards [h] with ω hω
  simp only [smul_eq_mul] at hω
  exact hω.congr (fun n => by ring)

/-- Textbook restatement of the strong law of large numbers: a direct alias of
`strong_law_of_large_numbers_real` matching the formulation from Lecture 6. -/
theorem textbook_strong_law_ae
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / (n : ℝ))
      atTop (𝓝 (∫ x, X 0 x ∂μ)) :=
  strong_law_of_large_numbers_real X hint hindep hident

end StrongLaw
