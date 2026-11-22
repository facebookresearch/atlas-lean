/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

/-- A real sequence is a function from the natural numbers to the reals, i.e. `ℕ → ℝ`. -/
def RealSequence := ℕ → ℝ

/-- A real sequence `x` is bounded if there exists a non-negative real `B` such that
`|x n| ≤ B` for every `n : ℕ`. -/
def IsBoundedSeq (x : ℕ → ℝ) : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |x n| ≤ B

/-- ε–N characterization of convergence: `x n → L` if and only if for every `ε > 0`
there exists `M : ℕ` such that `|x n - L| < ε` for all `n ≥ M`. -/
theorem seq_converges_iff (x : ℕ → ℝ) (L : ℝ) :
    Filter.Tendsto x Filter.atTop (nhds L) ↔
    ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, |x n - L| < ε := by
  rw [Metric.tendsto_atTop]
  simp_rw [Real.dist_eq]

/-- Squeeze (sandwich) theorem for real sequences: if `a n ≤ x n ≤ b n` for all `n`
and both `a` and `b` converge to the same limit `L`, then `x` also converges to `L`. -/
theorem squeeze_theorem (a x b : ℕ → ℝ) (L : ℝ)
    (hab : ∀ n, a n ≤ x n) (hxb : ∀ n, x n ≤ b n)
    (ha : Filter.Tendsto a Filter.atTop (nhds L))
    (hb : Filter.Tendsto b Filter.atTop (nhds L)) :
    Filter.Tendsto x Filter.atTop (nhds L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hab hxb

end Sequences
