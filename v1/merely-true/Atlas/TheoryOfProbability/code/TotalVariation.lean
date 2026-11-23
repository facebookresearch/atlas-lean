/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

/-- The **total variation distance** between two measures `μ` and `ν`, defined as
`‖μ - ν‖ = sup_B |μ(B) - ν(B)|` where the supremum runs over all measurable sets `B`. -/
noncomputable def totalVariationDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : ℝ :=
  ⨆ (s : Set Ω) (_ : MeasurableSet s), |(μ s).toReal - (ν s).toReal|
