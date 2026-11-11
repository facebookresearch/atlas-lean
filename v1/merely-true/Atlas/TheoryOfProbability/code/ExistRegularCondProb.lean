/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.RegularConditionalDistribution

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- **Existence of regular conditional probabilities.** When `Ω` is a standard Borel
space (a "nice" space), for any finite measure `μ` and measurable maps `X : α → β`,
`Y : α → Ω`, there exists a Markov kernel `κ : Kernel β Ω` that is a regular conditional
distribution of `Y` given `X`. -/
theorem exists_regularConditionalDistribution
    {α β Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel β Ω, IsRegularConditionalDistribution κ Y X μ :=
  ⟨condDistrib Y X μ, condDistrib_isRegularConditionalDistribution hX hY⟩

end ProbabilityTheory

end
