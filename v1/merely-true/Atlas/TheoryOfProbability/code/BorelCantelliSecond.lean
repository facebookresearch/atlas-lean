/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.BorelCantelli

open MeasureTheory ProbabilityTheory Filter

/-- **Second Borel–Cantelli lemma.** If the events `Aₙ` are (mutually) independent
and `∑ₙ μ(Aₙ) = ∞`, then almost every point belongs to infinitely many of the
`Aₙ`, i.e. `μ(limsup Aₙ) = 1`. -/
theorem second_Borel_Cantelli {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {A : ℕ → Set Ω}
    (hm : ∀ n, MeasurableSet (A n))
    (hindep : iIndepSet A μ)
    (hsum : ∑' n, μ (A n) = ⊤) :
    μ (limsup A atTop) = 1 :=
  measure_limsup_eq_one hm hindep hsum
