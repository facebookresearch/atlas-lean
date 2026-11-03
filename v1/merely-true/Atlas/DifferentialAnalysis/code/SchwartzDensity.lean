/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped ENNReal

noncomputable section

namespace SchwartzDensity

open MeasureTheory

/-- Density of Schwartz functions in `L^p`: for `1 ≤ p < ∞`, the canonical continuous
linear inclusion `SchwartzMap.toLpCLM` of `𝓢(ℝⁿ, ℂ)` into `Lᵖ(ℝⁿ, ℂ)` has dense range. -/
theorem schwartz_dense_Lp (n : ℕ) {p : ℝ≥0∞} (hp : p ≠ ⊤) [Fact (1 ≤ p)] :
    DenseRange
      (SchwartzMap.toLpCLM (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) ℂ p volume) :=
  SchwartzMap.denseRange_toLpCLM hp

end SchwartzDensity

end
