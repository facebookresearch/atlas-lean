/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Measure

namespace MeasureTheory.Measure

/-- The `n`-fold convolution power of a measure `ν` on an additive commutative
measurable monoid. Defined recursively: `convPow ν 0 = δ_0` (Dirac at the additive
identity) and `convPow ν (n+1) = convPow ν n ∗ ν`. If `ν` is the law of `Y`, then
`convPow ν n` is the law of the sum of `n` i.i.d. copies of `Y`. -/
noncomputable def convPow {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    (ν : Measure M) : ℕ → Measure M
  | 0 => dirac 0
  | n + 1 => (ν.convPow n) ∗ ν

end MeasureTheory.Measure

/-- A measure `μ` on an additive commutative measurable monoid is **infinitely
divisible** if for every `n ≥ 1` there is a probability measure `ν` whose `n`-fold
convolution power equals `μ`. Equivalently, the corresponding random variable `X`
can, for every `n`, be written in law as the sum of `n` i.i.d. copies of some
random variable `Y`. -/
def IsInfinitelyDivisible {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    (μ : Measure M) : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ ν : Measure M, IsProbabilityMeasure ν ∧ μ = ν.convPow n
