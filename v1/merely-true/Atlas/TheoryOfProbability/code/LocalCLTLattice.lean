/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.LatticeRV
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-- `IsSpan μ h` asserts that `h > 0` and the support of `μ` (its atoms) is contained in some
arithmetic progression `a + h · ℤ`. Equivalently, `h` is a *span* of `μ`. -/
def IsSpan (μ : Measure ℝ) (h : ℝ) : Prop :=
  0 < h ∧ ∃ a : ℝ, ∀ x : ℝ, μ {x} ≠ 0 → ∃ j : ℤ, x = a + j * h

/-- `IsMaximalSpan μ h` says that `h` is the largest span of `μ`: every other span `h'` of `μ`
satisfies `h' ≤ h`. -/
def IsMaximalSpan (μ : Measure ℝ) (h : ℝ) : Prop :=
  IsSpan μ h ∧ ∀ h' : ℝ, IsSpan μ h' → h' ≤ h

/-- The density `n(x) = (2π σ²)^{-1/2} · exp(-x²/(2σ²))` of the centered Gaussian with
variance `σ²` evaluated at `x`. -/
def gaussianDensity (σ : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(x ^ 2 / (2 * σ ^ 2)))


end ProbabilityTheory
