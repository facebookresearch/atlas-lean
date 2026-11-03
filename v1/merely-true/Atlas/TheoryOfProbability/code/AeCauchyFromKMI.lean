/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter Finset

set_option maxHeartbeats 4000000

noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper function used in the Kolmogorov three-series / a.s. Cauchy arguments:
given a truncation level `A > 0` and a centering constant `c`, `gAc A c x`
equals `x · 1_{|y| ≤ A}(x) - c`, i.e. it truncates `x` to zero outside the
interval `[-A, A]` and then subtracts `c`. This is the form used to construct
the centered, truncated summands `Y_n - E Y_n` for which one applies
Kolmogorov's maximal inequality. -/
def gAc (A c : ℝ) : ℝ → ℝ := fun x => x * (Set.indicator {y | |y| ≤ A} 1 x) - c

end KolmogorovThreeSeries
