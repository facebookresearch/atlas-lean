/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

/-- A sequence `x : ℕ → ℝ` is monotone increasing (i.e. `Monotone x`) if and only if
each term is bounded above by its immediate successor: `x n ≤ x (n + 1)` for all `n`. -/
theorem monotone_increasing_iff (x : ℕ → ℝ) :
    Monotone x ↔ ∀ n : ℕ, x n ≤ x (n + 1) := by
  constructor
  · intro hm n
    exact hm (Nat.le_succ n)
  · exact monotone_nat_of_le_succ

/-- A monotone decreasing real sequence converges if and only if it is bounded below,
and in that case its limit equals the infimum of its range: a monotone decreasing
sequence `x` converges iff `BddBelow (Set.range x)`, and when bounded below, the
sequence converges to `⨅ n, x n`. -/
theorem monotone_decreasing_convergence (x : ℕ → ℝ) (hm : Antitone x) :
    ((∃ L, Filter.Tendsto x Filter.atTop (nhds L)) ↔ BddBelow (Set.range x)) ∧
    (BddBelow (Set.range x) → Filter.Tendsto x Filter.atTop (nhds (⨅ n, x n))) := by
  constructor
  · constructor
    · rintro ⟨L, hL⟩
      exact hL.bddBelow_range
    · intro hb
      exact ⟨⨅ n, x n, tendsto_atTop_ciInf hm hb⟩
  · exact tendsto_atTop_ciInf hm

end Sequences
