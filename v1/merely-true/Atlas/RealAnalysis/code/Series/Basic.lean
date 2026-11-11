/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Real_Analysis.Series

/-- A real series `∑ x n` is absolutely convergent if the series of absolute values
`∑ |x n|` is summable. -/
def AbsolutelyConvergent (x : ℕ → ℝ) : Prop := Summable (fun n => |x n|)

/-- Rearrangement theorem for absolutely convergent series: if `∑ |x n|` is summable
and `∑ x n` has sum `s`, then for any permutation `σ : ℕ ≃ ℕ` the rearranged series
`∑ x (σ n)` is also absolutely convergent and has the same sum `s`. -/
theorem abs_convergent_rearrangement (x : ℕ → ℝ) (σ : ℕ ≃ ℕ)
    (habs : Summable (fun n => |x n|)) (hsum : HasSum x s) :
    Summable (fun n => |x (σ n)|) ∧ HasSum (x ∘ σ) s := by
  exact ⟨(Equiv.summable_iff σ).mpr habs, (Equiv.hasSum_iff σ).mpr hsum⟩

open Filter Finset

/-- The series `∑ x n` converges if the sequence of partial sums
`s m = ∑ n ∈ range m, x n` converges to some real number `s`. -/
def SeriesConverges (x : ℕ → ℝ) : Prop :=
  ∃ s, Tendsto (fun m => ∑ n ∈ range m, x n) atTop (nhds s)

end Real_Analysis.Series
