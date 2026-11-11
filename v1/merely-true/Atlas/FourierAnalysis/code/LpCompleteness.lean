/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open MeasureTheory
open scoped ENNReal

namespace LpCompleteness

theorem lp_banach_space
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    CompleteSpace (Lp E p μ) :=
  inferInstance

theorem smooth_compactSupport_dense_Lp_Rn
    (n : ℕ) {p : ℝ≥0∞} (hp_top : p ≠ ⊤) [hp : Fact (1 ≤ p)] :
    Dense {f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n))) |
      ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ),
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp_top

end LpCompleteness
