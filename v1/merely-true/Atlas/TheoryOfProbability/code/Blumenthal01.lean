/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.ZeroOne

open MeasureTheory MeasurableSpace Filtration

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The *germ σ-algebra at `0`* of a filtration `𝓕` indexed by `NNReal`,
defined as the intersection `⋂_{t > 0} 𝓕_t`. For Brownian motion this is the
`𝓕_0^+` σ-algebra of events observable "immediately after" time `0`; Blumenthal's
0-1 law states that every such event has probability `0` or `1`. -/
@[reducible]
def germSigmaAlgebraZero (𝓕 : Filtration NNReal m) : MeasurableSpace Ω :=
  ⨅ t > (0 : NNReal), 𝓕 t

/-- Definitional unfolding: `germSigmaAlgebraZero 𝓕` equals the indexed infimum
`⨅ t > 0, 𝓕 t`. -/
lemma germSigmaAlgebraZero_eq_iInf (𝓕 : Filtration NNReal m) :
    germSigmaAlgebraZero 𝓕 = ⨅ t > (0 : NNReal), 𝓕 t := rfl

/-- An abstract specification of a *Brownian motion* `B : NNReal → Ω → E`
started at `x ∈ E`, adapted to a filtration `𝓕` on `(Ω, m, μ)`. The fields
require that `μ` is a probability measure, `B 0 = x` almost surely, `B` is
adapted, increments `B_t - B_s` are independent of `𝓕_s` for `s < t`, each
increment has *some* law on `E` (the Gaussian distribution in the standard
case), and the sample paths `t ↦ B_t ω` are continuous for a.e. `ω`. -/
structure IsBrownianMotion {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [TopologicalSpace E] (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  start : ∀ᵐ ω ∂μ, B 0 ω = x
  adapted : Adapted 𝓕 (fun t => B t)
  indep_incr : ∀ s t : NNReal, s < t →
    Indep (𝓕 s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  gaussian_incr : ∀ s t : NNReal, s < t →
    ∃ (ν : Measure E), Measure.map (fun ω => B t ω - B s ω) μ = ν
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal => B t ω)

/-- For any strictly positive time `t`, the germ σ-algebra at `0` is contained
in `𝓕 t`, since `𝓕 t` appears as one of the terms in the infimum
`⨅ s > 0, 𝓕 s`. -/
lemma germSigmaAlgebraZero_le_of_pos (𝓕 : Filtration NNReal m) {t : NNReal} (ht : 0 < t) :
    germSigmaAlgebraZero 𝓕 ≤ 𝓕 t := by
  rw [germSigmaAlgebraZero_eq_iInf]
  exact iInf₂_le t ht




end ProbabilityTheory
