/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory Complex

namespace ProbabilityTheory

/-- The **characteristic function** of a probability measure `μ` on `ℝ`, defined by
`φ(t) = ∫ exp(i t x) dμ(x)`. For a random variable `X` with law `μ` this is
`φ_X(t) = E[exp(i t X)]`. -/
noncomputable def charFun (μ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * ↑t * ↑x) ∂μ

/-- The local `charFun` defined here agrees with Mathlib's `MeasureTheory.charFun`
on real measures, up to rearranging the order of multiplication inside the
exponential. -/
lemma charFun_eq_measureTheory_charFun (μ : Measure ℝ) (t : ℝ) :
    charFun μ t = MeasureTheory.charFun μ t := by
  simp only [charFun, MeasureTheory.charFun_apply_real]
  congr 1 with x
  ring_nf

end ProbabilityTheory
