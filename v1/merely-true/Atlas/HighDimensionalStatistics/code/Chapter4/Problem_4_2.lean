/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.unusedVariables false

open MeasureTheory Matrix Finset

noncomputable section

namespace Chapter4.Problem42

/-- Squared Frobenius norm of a `Fin m × Fin p` real matrix. -/
def frobSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Operator (spectral) norm of `A`, defined as the supremum of `‖A v‖` over unit vectors `v`. -/
noncomputable def opNorm {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  sSup {x : ℝ | ∃ (v : Fin p → ℝ), ‖v‖ = 1 ∧ x = ‖A.mulVec v‖}

end Chapter4.Problem42

end
