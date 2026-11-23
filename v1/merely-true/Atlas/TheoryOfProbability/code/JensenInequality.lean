/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Integral

open MeasureTheory MeasureTheory.Measure

/-- **Jensen's inequality.** If `μ` is a probability measure on `Ω`, `X : Ω → ℝ` is integrable,
and `φ : ℝ → ℝ` is convex (and `φ ∘ X` is integrable), then
`φ (∫ X dμ) ≤ ∫ φ(X) dμ`. In particular, for a random variable `X` with finite mean,
`φ(𝔼 X) ≤ 𝔼 φ(X)`. -/
theorem jensen_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ)
    {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφX_int : Integrable (φ ∘ X) μ) :
    φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ :=
  hφ_convex.map_integral_le (hφ_convex.continuousOn isOpen_univ) isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hX_int hφX_int
