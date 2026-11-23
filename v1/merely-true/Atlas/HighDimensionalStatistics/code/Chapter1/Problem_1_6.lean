/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open MeasureTheory Real Set Metric
open scoped ENNReal NNReal

noncomputable section

/-- A random vector `X : Ω → ℝ^p` is sub-Gaussian with variance proxy `σ²`
if every unit-norm linear projection `ω ↦ ⟨θ, X ω⟩` is sub-Gaussian with
proxy `σ²`. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin p)) (σsq : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin p), ‖θ‖ = 1 →
    IsSubGaussian (fun ω => @inner ℝ _ _ θ (X ω)) σsq μ


end
