/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Claim21Lec10
import Atlas.BooleanFunctions.code.GaussianStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

def signFn : ℝ → ℝ := fun x => if x ≥ 0 then 1 else -1

def gaussianNoiseStabilitySign (ρ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, signFn p.1 * signFn p.2 ∂(rhoCorrelatedGaussian ρ)



end GaussianStability

end
