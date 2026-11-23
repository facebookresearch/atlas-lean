/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable

open scoped MeasureTheory NNReal ENNReal
open MeasureTheory

namespace TheoryOfProbability3

variable {α : Type*} {ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- Textbook (Durrett) definition of uniform integrability of a family of real-valued
functions `f : ι → α → ℝ` with respect to a measure `μ`: each `f i` is
`AEStronglyMeasurable`, and for every `ε > 0` there is a uniform truncation level
`C : ℝ≥0` so that the tail `L¹` mass `∫ |f i| · 1_{C ≤ ‖f i‖} dμ ≤ ε` for every `i`.
This matches the textbook formulation `lim_{M→∞} sup_i E(|X_i|; |X_i| > M) = 0`. -/
def TextbookUniformlyIntegrable (f : ι → α → ℝ) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ≥0, ∀ i, eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε

end TheoryOfProbability3
