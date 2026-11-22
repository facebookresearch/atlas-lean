/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

namespace MarkovInequality

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Theorem 3.3.1 (Markov's inequality).** For a nonnegative integrable random variable
$X$ and any $a > 0$, $\mathbb{P}(X \geq a) \leq \mathbb{E}[X] / a$. -/
theorem markov_inequality {X : Ω → ℝ} (hX_nonneg : 0 ≤ᵐ[μ] X)
    (hX_int : Integrable X μ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂μ) / a := by
  rw [le_div_iff₀ ha]
  have h := mul_meas_ge_le_integral_of_nonneg hX_nonneg hX_int a
  linarith

end MarkovInequality
