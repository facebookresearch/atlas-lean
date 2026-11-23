/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory Measure Set

/-- **Radon–Nikodym theorem** (density form). If `ν ≪ μ` (with `ν` having a Lebesgue
decomposition w.r.t. `μ`), then `ν` is the measure with density `dν/dμ` w.r.t. `μ`, i.e.
`μ.withDensity (ν.rnDeriv μ) = ν`. -/
theorem radon_nikodym_withDensity {Ω : Type*} {𝓕 : MeasurableSpace Ω}
    (μ ν : Measure Ω) [HaveLebesgueDecomposition ν μ] (hac : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hac

/-- **Radon–Nikodym theorem** (integral form). If `ν ≪ μ` then for every measurable set `A`,
`ν(A) = ∫_A (dν/dμ) dμ`, expressing `ν` as integration of its Radon–Nikodym derivative
against `μ`. -/
theorem radon_nikodym_setLIntegral' {Ω : Type*} {𝓕 : MeasurableSpace Ω}
    (μ ν : Measure Ω) [HaveLebesgueDecomposition ν μ] [SFinite μ]
    (hac : ν ≪ μ) (A : Set Ω) :
    ∫⁻ x in A, ν.rnDeriv μ x ∂μ = ν A :=
  Measure.setLIntegral_rnDeriv hac A
