/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory

/-- **Definition 1.11 (Sub-exponential random variable).** A real-valued random
variable `X` is sub-exponential with parameter `λ > 0` if it is centered
(integrable with mean zero) and its moment generating function is bounded by
the Gaussian MGF on the strip `|s| ≤ 1/λ`:
`E[exp(sX)] ≤ exp(s² λ² / 2)` for all such `s`. -/
def IsSubExponential {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (lambda : ℝ) : Prop :=
  0 < lambda ∧
  Integrable X μ ∧
  ∫ ω, X ω ∂μ = 0 ∧
  ∀ s : ℝ, |s| ≤ 1 / lambda →
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * lambda ^ 2 / 2)
