/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

/-- `y` is a subsequence of `x` if there is a strictly increasing index function
`φ : ℕ → ℕ` such that `y = x ∘ φ` (i.e. `y k = x (φ k)`). -/
def IsSubsequence (x y : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ y = x ∘ φ

/-- Bolzano–Weierstrass theorem for real sequences: every bounded real sequence has a
convergent subsequence, i.e. a strictly increasing `φ : ℕ → ℕ` and a limit `L : ℝ`
with `x ∘ φ → L`. -/
theorem bolzano_weierstrass (x : ℕ → ℝ) (hb : Bornology.IsBounded (Set.range x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, Filter.Tendsto (x ∘ φ) Filter.atTop (nhds L) := by
  obtain ⟨a, _, φ, hφ, ha⟩ := tendsto_subseq_of_bounded hb (fun n => Set.mem_range_self n)
  exact ⟨φ, hφ, a, ha⟩

/-- If a real sequence `x` converges to `L`, then every subsequence `x ∘ φ` (with
`φ : ℕ → ℕ` strictly increasing) also converges to `L`. -/
theorem subseq_tendsto (x : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hx : Filter.Tendsto x Filter.atTop (nhds L)) :
    Filter.Tendsto (x ∘ φ) Filter.atTop (nhds L) :=
  hx.comp hφ.tendsto_atTop

end Sequences
