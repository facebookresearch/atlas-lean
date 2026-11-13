/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.CharFun

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal

noncomputable section

namespace ProbabilityTheory

/-- The **Lindeberg condition** for a triangular array `X n k` of random variables on `(Ω, μ)`:
for every `ε > 0`, the truncated second moment
`∑ₖ ∫ (X n k)² · 𝟙{|X n k| > ε} dμ` tends to `0` as `n → ∞`. This is the key hypothesis of the
Lindeberg–Feller central limit theorem. -/
def LindebergConditionTriangular {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)
    atTop (𝓝 0)





end ProbabilityTheory
