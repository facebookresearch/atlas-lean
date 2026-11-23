/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory

noncomputable section

namespace ConditionalExpectation

/-- The **conditional expectation** of `f : Ω → ℝ` given the sub-σ-algebra `m`,
under the measure `μ`.

Following the textbook definition, given a probability space `(Ω, m₀, μ)`, a sub-σ-field
`m ⊆ m₀`, and a random variable `f` measurable w.r.t. `m₀` with `E|f| < ∞`, the conditional
expectation `μ[f | m]` is an `m`-measurable random variable `Y` such that
`∫_A f dμ = ∫_A Y dμ` for every `A ∈ m`. -/
def condExp {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ :=
  μ[f | m]

end ConditionalExpectation

end
