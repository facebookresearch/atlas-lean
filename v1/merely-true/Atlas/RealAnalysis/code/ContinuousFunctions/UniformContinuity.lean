/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Metric

namespace Real_Analysis

/-- A real function `f` is uniformly continuous on a set `S ⊆ ℝ` if and only if it
satisfies the textbook ε–δ criterion: for every `ε > 0` there exists `δ > 0` such
that `|f x - f y| < ε` for all `x, y ∈ S` with `|x - y| < δ`. -/
theorem uniform_continuous_on_iff (f : ℝ → ℝ) (S : Set ℝ) :
    UniformContinuousOn f S ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |x - y| < δ → |f x - f y| < ε := by
  simp only [Metric.uniformContinuousOn_iff, Real.dist_eq]

end Real_Analysis
