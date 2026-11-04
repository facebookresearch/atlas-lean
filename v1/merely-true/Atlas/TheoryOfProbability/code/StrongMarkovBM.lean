/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.StoppingTimeContinuous
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal

noncomputable section

namespace BrownianMotion

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The process obtained from `B` by shifting time by the stopping time `T` and
recentering at `B(T)`: `t ↦ B(T + t) - B(T)`. -/
def stoppedShiftedProcess (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B ((T ω).toNNReal + t) ω - B ((T ω).toNNReal) ω

end BrownianMotion

