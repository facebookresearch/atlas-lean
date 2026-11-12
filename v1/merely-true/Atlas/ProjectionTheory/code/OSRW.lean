/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped ENNReal

noncomputable section

namespace ProjectionTheory

/-- Orthogonal projection of a point `x ∈ ℝ²` onto the line through the origin
making angle `θ` with the $x$-axis: $\pi_\theta(x) = x_0 \cos\theta + x_1 \sin\theta$. -/
def orthProj (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * Real.cos θ + x 1 * Real.sin θ

/-- The Hausdorff-dimension exceptional set: the set of directions `θ` for which the
orthogonal projection `orthProj θ '' X` of `X ⊂ ℝ²` has Hausdorff dimension strictly
less than `s`. -/
def exceptionalSetHD (X : Set (EuclideanSpace ℝ (Fin 2))) (s : ℝ≥0∞) : Set ℝ :=
  {θ : ℝ | dimH (orthProj θ '' X) < s}


end ProjectionTheory
