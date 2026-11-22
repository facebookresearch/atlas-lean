/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.CharacteristicFunction
import Atlas.TheoryOfProbability.code.WeakConvergence
import Mathlib.MeasureTheory.Measure.LevyConvergence

open MeasureTheory Complex Filter ProbabilityTheory
open scoped Topology BoundedContinuousFunction

noncomputable section

namespace ProbabilityTheory

/-- Weak convergence of the underlying measures `μs n` to `μ` is equivalent to convergence of
`μs n` to `μ` in the topology on `ProbabilityMeasure ℝ`. A bridge between the project's
`WeakConvergence` definition and Mathlib's `ProbabilityMeasure` topology. -/
theorem weakConvergence_iff_tendsto
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ) :
    WeakConvergence (fun n ↦ (μs n : Measure ℝ)) (μ : Measure ℝ) ↔
      Tendsto μs atTop (𝓝 μ) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.symm

/-- **Lévy's continuity theorem** (backward direction): if the characteristic functions of a
sequence of probability measures `μs n` on `ℝ` converge pointwise to the characteristic function
of `μ`, then `μs n` converges weakly to `μ`. -/
theorem levy_continuity_backward
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (↑(μs n)) t) atTop (𝓝 (charFun (↑μ) t))) :
    WeakConvergence (fun n ↦ (μs n : Measure ℝ)) (μ : Measure ℝ) := by
  rw [weakConvergence_iff_tendsto]
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp_rw [← charFun_eq_measureTheory_charFun]
  exact h t

end ProbabilityTheory
