/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.CharacteristicFunction

open MeasureTheory Complex

namespace ProbabilityTheory

/-- A probability measure `μ` on `ℝ` corresponds to a **lattice random variable** when its
characteristic function `charFun μ` equals `1` at some nonzero `l` (so `μ` is supported on a
translate of `(2π/l)ℤ`) but is not identically `1` (so `μ` is not a point mass at `0`). -/
def IsLatticeRV (μ : Measure ℝ) : Prop :=
  (∃ l : ℝ, l ≠ 0 ∧ charFun μ l = 1) ∧ ¬(∀ t : ℝ, charFun μ t = 1)

end ProbabilityTheory
