/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false

open MeasureTheory Filtration ProbabilityTheory Filter

noncomputable section

namespace BrownianFiltration

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `IsBrownianMotion d B 𝓕 μ x` says that `B : NNReal → Ω → (Fin d → ℝ)` is a
`d`-dimensional Brownian motion started at `x` under the probability measure `μ`,
adapted to the filtration `𝓕`. The defining properties are: `μ` is a probability
measure, `B 0 = x` a.s., `B t` is `𝓕 t`-measurable in each coordinate, increments
`B t - B s` (for `s ≤ t`) are independent of `𝓕 s` and Gaussian with variance `t - s`,
and the paths `t ↦ B t ω` are a.s. continuous. -/
structure IsBrownianMotion (d : ℕ)
    (B : NNReal → Ω → (Fin d → ℝ)) (𝓕 : Filtration NNReal m) (μ : Measure Ω)
    (x : Fin d → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  start : ∀ᵐ ω ∂μ, B 0 ω = x
  adapted : ∀ t : NNReal, ∀ i : Fin d,
    Measurable[𝓕 t, inferInstance] (fun ω => B t ω i)
  indep_incr : ∀ (s t : NNReal), s ≤ t →
    ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (𝓕 s) (μ := μ)
  gaussian_incr : ∀ (s t : NNReal) (h : s ≤ t) (i : Fin d),
    μ.map (fun ω => B t ω i - B s ω i) =
      ProbabilityTheory.gaussianReal 0
        ⟨(t : ℝ) - (s : ℝ), sub_nonneg.mpr (NNReal.coe_le_coe.mpr h)⟩
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal => B t ω)

section ExpectationEquivalence


end ExpectationEquivalence

section BrownianRightContinuity


end BrownianRightContinuity

end BrownianFiltration

section CondExpRightCont

end CondExpRightCont

