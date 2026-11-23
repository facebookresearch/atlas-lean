/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Kernel.Defs

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- A **transition probability** from `α` to `β` is a function `p : α × 𝓢_β → ℝ` such that
(1) for each `x ∈ α`, `A ↦ p(x, A)` is a probability measure on `(β, 𝓢_β)`, and
(2) for each `A ∈ 𝓢_β`, the map `x ↦ p(x, A)` is measurable.
In Mathlib this is precisely an `IsMarkovKernel`. -/
abbrev IsTransitionProbability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) : Prop :=
  IsMarkovKernel κ

namespace IsTransitionProbability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {κ : Kernel α β}

end IsTransitionProbability

end ProbabilityTheory
