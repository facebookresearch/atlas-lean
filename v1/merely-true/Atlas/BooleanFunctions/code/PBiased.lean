/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi

open scoped NNReal
open MeasureTheory Measure PMF

namespace BooleanFourier

noncomputable def pBiasedBit (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance pBiasedBit.instIsProbabilityMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (pBiasedBit p hp) :=
  PMF.toMeasure.isProbabilityMeasure _

noncomputable def pBiasedMeasure (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (Fin n → Bool) :=
  Measure.pi (fun _ => pBiasedBit p hp)

instance pBiasedMeasure.instIsProbabilityMeasure (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (pBiasedMeasure n p hp) :=
  Measure.pi.instIsProbabilityMeasure _

end BooleanFourier
