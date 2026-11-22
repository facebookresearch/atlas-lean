/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

/-- **Markov's inequality**. Let `X` be a non-negative integrable random variable on the
probability space `(Ω, μ)` and let `a > 0`. Then

  `μ{ω | a ≤ X ω} ≤ (∫ X dμ) / a`. -/
theorem markov_inequality {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[μ] X) (hX_int : Integrable X μ)
    {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂μ) / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hX_nn hX_int a
