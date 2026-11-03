/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.Sheppard

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace GaussianStability

def thresholdAtLevel (t : ℝ) : ℝ → ℝ :=
  fun x => if x ≥ t then (1 : ℝ) else -1

def thresholdFn (c : ℝ) : ℝ → ℝ :=
  thresholdAtLevel (Classical.epsilon (fun t =>
    ∫ x, thresholdAtLevel t x ∂(gaussianReal 0 1) = c))

lemma thresholdAtLevel_range (t : ℝ) (x : ℝ) :
    thresholdAtLevel t x ∈ Icc (-1 : ℝ) 1 := by
  simp only [thresholdAtLevel]
  split_ifs <;> norm_num

lemma thresholdFn_range (c : ℝ) (x : ℝ) :
    thresholdFn c x ∈ Icc (-1 : ℝ) 1 := by
  unfold thresholdFn
  exact thresholdAtLevel_range _ x


end GaussianStability

end
