/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Atlas.TheoryOfProbability.code.BochnerTheorem
import Atlas.TheoryOfProbability.code.DomainAttraction

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal

set_option maxHeartbeats 3200000

noncomputable section

namespace ProbabilityTheory

/-- The convolution of the Dirac measure at `0` with itself is again the Dirac measure
at `0`: `δ₀ ∗ δ₀ = δ₀`. A small computational lemma supporting the construction of
stable distributions via convolutions. -/
lemma measureConv_dirac_zero :
    measureConv (Measure.dirac (0 : ℝ)) (Measure.dirac (0 : ℝ)) = Measure.dirac 0 := by
  simp [measureConv, Measure.dirac_prod_dirac]

end ProbabilityTheory
