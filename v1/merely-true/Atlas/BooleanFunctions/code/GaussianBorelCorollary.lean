/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Borel

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace

namespace GaussianStability

variable {n : ℕ}

def IsPlusMinusOneValued (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

def gaussianNoiseStabilityPM (ρ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, ∫ z, f x * f (ρ • x + Real.sqrt (1 - ρ ^ 2) • z)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

def IsHalfspaceThreshold (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (w : EuclideanSpace ℝ (Fin n)) (t : ℝ), w ≠ 0 ∧
    ∀ x, f x = if ⟪w, x⟫_ℝ ≤ t then 1 else -1

def gaussianMean (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))



end GaussianStability

end
