/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

open MeasureTheory Measure

/-- **Definition (Absolutely continuous).** For σ-finite measures `μ` and `ν` on
`(Ω, 𝓕)`, `ν` is absolutely continuous with respect to `μ`, written `ν ≪ μ`, if
and only if every `μ`-null set `A ⊆ Ω` (i.e. `μ A = 0`) is also `ν`-null
(i.e. `ν A = 0`). This lemma unfolds the Mathlib definition into this explicit
characterization. -/
theorem absolutelyContinuous_def {Ω : Type*} {𝓕 : MeasurableSpace Ω}
    (μ ν : Measure Ω) :
    ν ≪ μ ↔ ∀ A : Set Ω, μ A = 0 → ν A = 0 := by
  constructor
  · intro h A hA
    exact h hA
  · intro h A hA
    exact h A hA
