/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- **First Borel–Cantelli lemma.** If `∑ₙ μ(Aₙ) < ∞`, then the set of points belonging
to infinitely many of the `Aₙ` has measure zero, i.e. `μ(limsup Aₙ) = 0`. -/
theorem first_borel_cantelli {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {A : ℕ → Set Ω} (hA : ∑' n, μ (A n) ≠ ⊤) :
    μ (limsup A atTop) = 0 :=
  measure_limsup_atTop_eq_zero hA
