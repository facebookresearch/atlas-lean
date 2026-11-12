/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

open MeasureTheory Measure Set TopologicalSpace
open scoped CompactlySupported ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

section RieszMeasureBorel

open RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

/-- The Riesz representation measure of a positive linear functional on compactly supported
continuous functions is a Borel measure: every Borel set is Caratheodory measurable with respect
to its outer measure. -/
theorem rieszMeasure_isBorelMeasure
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    borel X ≤ (rieszMeasure Λ).toOuterMeasure.caratheodory := by
  have h := le_toOuterMeasure_caratheodory (rieszMeasure Λ)
  rwa [← BorelSpace.measurable_eq]

/-- The Riesz representation measure associated to a positive linear functional on `C₀(X, ℝ)`
is a Borel measure. -/
theorem rieszMeasureC0_isBorelMeasure
    (Λ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    borel X ≤ (rieszMeasureOfC0Functional Λ hΛ).toOuterMeasure.caratheodory :=
  rieszMeasure_isBorelMeasure (restrictC0ToCc Λ hΛ)

end RieszMeasureBorel

end MeasuresAndSigmaAlgebras
