/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Poisson.Basic

open scoped ENNReal NNReal Nat
open Real MeasureTheory ProbabilityTheory

noncomputable section

/-- `IsPoissonRV X μ r` says that `X : Ω → ℕ` is a Poisson random variable with parameter
`r ≥ 0` under the measure `μ`: for every `k ∈ ℕ`, `P(X = k) = r^k e^{-r} / k!` (Lecture 17,
*Definition (Poisson random variable)*). -/
def IsPoissonRV {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℕ) (μ : Measure Ω) (r : ℝ≥0) : Prop :=
  ∀ k : ℕ, μ (X ⁻¹' {k}) = ENNReal.ofReal (poissonPMFReal r k)

end
