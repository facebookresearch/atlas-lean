/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory MeasurableSpace Measure ENNReal

noncomputable section

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [SFinite μ] [SFinite ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Fubini's theorem**. For σ-finite (here `SFinite`) measures `μ` on `α` and `ν` on `β`
and a function `f : α × β → E` that is integrable w.r.t. the product measure `μ.prod ν`,
the integral of `f` over the product space agrees with both iterated integrals, and the
two iterated integrals agree with each other:
`∫_{α × β} f d(μ × ν) = ∫_α ∫_β f(x,y) dν dμ = ∫_β ∫_α f(x,y) dμ dν`. -/
theorem fubini_theorem (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ ∧
    ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν ∧
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
  ⟨integral_prod f hf, integral_prod_symm f hf,
    (integral_prod f hf).symm.trans (integral_prod_symm f hf)⟩

end
