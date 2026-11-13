/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.OUSemigroup
import Atlas.BooleanFunctions.code.GaussianStability

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}

theorem gaussianNoiseOperator_eq_ornsteinUhlenbeckOp (ρ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    gaussianNoiseOperator ρ f = GaussianSpace.ornsteinUhlenbeckOp ρ f := by
  rfl

end GaussianStability
