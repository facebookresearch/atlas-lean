/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Real

/--
Moment generating function (Lecture 8): for a real-valued random variable `X`
with law `μ`, the moment generating function is `M_X(t) = E[e^{tX}]`, defined
here as the Bochner integral `∫ exp (t · X ω) ∂μ`.
-/
noncomputable def momentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * X ω) ∂μ
