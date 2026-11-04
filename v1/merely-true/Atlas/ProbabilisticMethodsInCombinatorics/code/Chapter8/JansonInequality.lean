/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Real Finset BigOperators MeasureTheory

namespace JansonInequality


set_option maxHeartbeats 400000

/-- **Janson inequality II** (Theorem 8.1.8). If $\Delta \geq \mu$ and for all $q \in [0,1]$
the bound $v \leq \exp(-q\mu + q^2 \Delta / 2)$ holds, then $v \leq \exp(-\mu^2/(2\Delta))$
(obtained by optimizing at $q = \mu/\Delta$). In particular this gives
$\Pr(X = 0) \leq \exp(-\mu^2/(2\Delta))$. -/
theorem janson_inequality_II
    {μ Δ v : ℝ} (hμ_pos : 0 < μ) (hΔ_ge_μ : Δ ≥ μ)
    (hbound : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → v ≤ Real.exp (-q * μ + q ^ 2 * Δ / 2)) :
    v ≤ Real.exp (-(μ ^ 2) / (2 * Δ)) := by
  have hΔ_pos : (0 : ℝ) < Δ := lt_of_lt_of_le hμ_pos hΔ_ge_μ
  have hq_nonneg : (0 : ℝ) ≤ μ / Δ := div_nonneg (le_of_lt hμ_pos) (le_of_lt hΔ_pos)
  have hq_le_one : μ / Δ ≤ 1 := div_le_one_of_le₀ hΔ_ge_μ (le_of_lt hΔ_pos)
  have key := hbound (μ / Δ) hq_nonneg hq_le_one
  suffices h : -(μ / Δ) * μ + (μ / Δ) ^ 2 * Δ / 2 = -(μ ^ 2) / (2 * Δ) by
    rwa [h] at key
  field_simp
  ring

end JansonInequality
