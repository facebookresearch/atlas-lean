/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Kernel.CondDistrib

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

noncomputable section

/-- **Regular conditional distribution (textbook form).** A family of measures
`μ_rcd : Ω → Measure S` is a regular conditional distribution for `X` given the
sub-σ-algebra `𝒢` under `P` if:
(1) for every measurable `A ⊆ S`, the map `ω ↦ μ_rcd ω A` is a version of
`P(X ∈ A | 𝒢)`, and
(2) for `P`-a.e. `ω`, the map `A ↦ μ_rcd ω A` is a probability measure. -/
structure RegularConditionalDistribution
    {Ω : Type*} {S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]
    (μ_rcd : Ω → Measure S) (X : Ω → S) (𝒢 : MeasurableSpace Ω) (P : Measure Ω) : Prop where
  ae_eq_condexp : ∀ {A : Set S}, MeasurableSet A →
    (fun ω => (μ_rcd ω A).toReal) =ᵐ[P] P⟦X ⁻¹' A | 𝒢⟧
  ae_isProbabilityMeasure : ∀ᵐ ω ∂P, IsProbabilityMeasure (μ_rcd ω)

namespace ProbabilityTheory

/-- **Regular conditional distribution (kernel form).** A Markov kernel
`κ : Kernel β Ω` is a regular conditional distribution of `Y : α → Ω` given
`X : α → β` under `μ` if for every measurable `s ⊆ Ω`, the function
`a ↦ κ (X a) s` is a version of the conditional probability
`μ(Y ∈ s | σ(X))`. -/
structure IsRegularConditionalDistribution
    {α : Type*} {β : Type*} {Ω : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace Ω]
    (κ : Kernel β Ω) (Y : α → Ω) (X : α → β) (μ : Measure α) : Prop where
  isMarkovKernel : IsMarkovKernel κ
  ae_eq_condExp : ∀ {s : Set Ω}, MeasurableSet s →
    (fun a => (κ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧

/-- When `Ω` is a standard Borel space, Mathlib's `condDistrib Y X μ` is a
regular conditional distribution of `Y` given `X` under `μ`. This packages
`condDistrib_ae_eq_condExp` together with the Markov-kernel property. -/
theorem condDistrib_isRegularConditionalDistribution
    {α β Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ where
  isMarkovKernel := inferInstance
  ae_eq_condExp hs := condDistrib_ae_eq_condExp hX hY hs

end ProbabilityTheory

end
