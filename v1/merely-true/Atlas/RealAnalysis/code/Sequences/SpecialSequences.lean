/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter Real Topology

namespace Sequences

/-- Some special sequences:
1. If `p > 0`, then `n^(-p) → 0` as `n → ∞`.
2. If `p > 0`, then `p^(1/n) → 1` as `n → ∞`.
3. `n^(1/n) → 1` as `n → ∞`. -/
theorem special_sequences :
    (∀ p : ℝ, 0 < p → Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) Filter.atTop (nhds 0)) ∧
    (∀ p : ℝ, 0 < p → Filter.Tendsto (fun n : ℕ => p ^ ((1 : ℝ) / n)) Filter.atTop (nhds 1)) ∧
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / n)) Filter.atTop (nhds 1) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro p hp
    exact (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
  ·
    intro p hp
    have h : Filter.Tendsto (fun n : ℕ => p ^ ((n : ℝ)⁻¹)) Filter.atTop (nhds 1) := by
      have hcont : Continuous (p ^ · : ℝ → ℝ) :=
        continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow hp.ne'
      exact (hcont.tendsto' 0 1 (rpow_zero p)).comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    have heq : (fun n : ℕ => p ^ ((1 : ℝ) / (n : ℝ))) = (fun n : ℕ => p ^ ((n : ℝ)⁻¹)) := by
      ext n; congr 1; ring
    rwa [heq]
  ·
    exact tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

end Sequences
