/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter ProbabilityTheory
open scoped Topology BoundedContinuousFunction

noncomputable section

/-- **Weak convergence** of a sequence of measures `μseq` on `ℝ` to `μ`, expressed via
bounded continuous test functions: `∫ f d(μseq n) → ∫ f dμ` for every `f : ℝ →ᵇ ℝ`. -/
def ConvergesWeakly (μseq : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ (f : ℝ →ᵇ ℝ), Tendsto (fun n => ∫ x, f x ∂(μseq n)) atTop (𝓝 (∫ x, f x ∂μ))

/-- **Convergence in distribution** of a sequence of measures `μseq` on `ℝ` to `μ`, expressed
via cumulative distribution functions: `F_{μseq n}(x) → F_μ(x)` at every continuity point `x`
of `F_μ`. This is the textbook definition `X_n ⇒ X` (Lecture 12). -/
def ConvergesInDistributionCDF (μseq : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (fun y => ((μ (Set.Iic y)).toReal)) x →
    Tendsto (fun n => ((μseq n) (Set.Iic x)).toReal) atTop
      (𝓝 ((μ (Set.Iic x)).toReal))

namespace ProbabilityTheory

/-- **Weak convergence** of a sequence of probability measures `μs` on `ℝ` to a probability
measure `μ`: shorthand for `ConvergesWeakly μs μ`. -/
def WeakConvergence (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ConvergesWeakly μs μ

end ProbabilityTheory
