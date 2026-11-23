/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SimpleApproximationFix
import Atlas.DifferentialAnalysis.code.MeasurabilityOfFunctions

open MeasureTheory MeasureTheory.SimpleFunc
open scoped ENNReal NNReal

namespace SimpleApproximation

variable {X : Type*} [MeasurableSpace X]

/-- Strict uniform approximation by the canonical simple-function approximants
`SimpleFunc.eapprox`: for any `ε > 0` there exists an index `N` such that for all
`n ≥ N`, the approximation error `f x − eapprox f n x` is strictly less than `ε`
uniformly over the bounded sublevel set `{x | f x ≤ c}`. -/
theorem eapprox_uniform_on_bounded_strict {f : X → ℝ≥0∞} (hf : Measurable f)
    (c : ℝ≥0) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, f x ≤ ↑c →
      f x - SimpleFunc.eapprox f n x < ε := by
  obtain ⟨N, hN⟩ := ennrealRatEmbed_dense_Icc (↑c) ENNReal.coe_ne_top ε hε
  exact ⟨N, fun n hn x hfx => by
    obtain ⟨k, hkN, hk_le, hk_diff⟩ := hN (f x) hfx
    have hkn : k < n := Nat.lt_of_lt_of_le hkN hn
    have heapprox_ge : ennrealRatEmbed k ≤ SimpleFunc.eapprox f n x :=
      eapprox_ge_ennrealRatEmbed hf hkn x hk_le
    calc f x - SimpleFunc.eapprox f n x
        ≤ f x - ennrealRatEmbed k := tsub_le_tsub_left heapprox_ge _
      _ < ε := hk_diff⟩

end SimpleApproximation
