/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Atlas.TheoryOfProbability.code.MartingaleOrthogonality
import Atlas.TheoryOfProbability.code.SubmartingaleConvergence
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.TFAE
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
open MeasureTheory Filter Topology

noncomputable section

/-- The **predictable quadratic variation** `Aₙ` of a process `f` with respect to a
filtration `ℱ`, defined as `Aₙ = ∑_{i=0}^{n-1} E[(f_{i+1} - f_i)² | ℱ_i]`. For a
square-integrable martingale this is the predictable increasing process arising
from Doob's decomposition of `f²`. -/
def predictableQuadVar {Ω : Type*} {m0 : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  fun n => ∑ i ∈ Finset.range n,
    μ[(fun ω => (f (i + 1) ω - f i ω) ^ 2) | ℱ i]

end
