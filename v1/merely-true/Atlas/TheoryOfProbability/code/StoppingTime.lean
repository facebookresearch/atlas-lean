/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Stopping

open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A `WithTop ℕ`-valued function `τ` is a discrete stopping time with respect to the
filtration `f` if for every `n : ℕ`, the event `{ω | τ ω = n}` is `f n`-measurable.

This is the textbook definition (Lecture 23): `T` is a stopping time when `{T = n} ∈ ℱ_n`
for every `n`. Allowing the value `⊤` lets the stopping time be infinite. -/
def IsDiscreteStoppingTime (f : Filtration ℕ m) (τ : Ω → WithTop ℕ) : Prop :=
  ∀ n : ℕ, MeasurableSet[f n] {ω | τ ω = ↑n}

/-- A discrete stopping time with respect to the filtration `f`: a `WithTop ℕ`-valued
function bundled with a proof that it satisfies `IsDiscreteStoppingTime`. -/
structure DiscreteStoppingTime (f : Filtration ℕ m) where
  val : Ω → WithTop ℕ
  property : IsDiscreteStoppingTime f val
