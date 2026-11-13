/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Real_Analysis

/-- A real sequence `x` is Cauchy (in the Mathlib sense, `CauchySeq x`) if and only if it
satisfies the textbook Cauchy criterion: for every `ε > 0` there exists `M : ℕ` such
that `|x n - x k| < ε` whenever `n, k ≥ M`. -/
theorem cauchy_seq_iff (x : ℕ → ℝ) :
    CauchySeq x ↔ ∀ ε > 0, ∃ M : ℕ, ∀ n k, n ≥ M → k ≥ M → |x n - x k| < ε := by
  rw [Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n k hn hk => by rw [← Real.dist_eq]; exact hN n hn k hk⟩
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    exact ⟨M, fun m hm n hn => by rw [Real.dist_eq]; exact hM m n hm hn⟩

/-- Cauchy completeness of the reals: a real sequence is Cauchy if and only if it
converges to some limit `L : ℝ`. -/
theorem cauchy_iff_convergent (x : ℕ → ℝ) :
    CauchySeq x ↔ ∃ L : ℝ, Filter.Tendsto x Filter.atTop (nhds L) := by
  constructor
  · exact cauchySeq_tendsto_of_complete
  · rintro ⟨L, hL⟩
    exact hL.cauchySeq

end Real_Analysis
