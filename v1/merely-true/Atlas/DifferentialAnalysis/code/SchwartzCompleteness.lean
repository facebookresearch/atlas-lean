/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Atlas.DifferentialAnalysis.code.SchwartzMetric

open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


/-- Auxiliary completeness statement: a Schwartz-seminorm-Cauchy sequence in `𝓢(E, F)`
converges to some Schwartz function in every seminorm `sup_{|α|,|β|≤K}`. -/
theorem schwartz_seminorm_cauchy_converges_aux
    (u : ℕ → 𝓢(E, F))
    (hcauchy : ∀ K : ℕ, ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - u m) < ε) :
    ∃ v : 𝓢(E, F), ∀ K : ℕ, Filter.Tendsto
      (fun n => (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - v))
      Filter.atTop (nhds 0) :=
  TemperedDistributions.schwartz_seminorm_cauchy_converges u hcauchy

/-- The Schwartz space `𝓢(E, F)` is complete (Melrose Prop. 6.7 / 7.4-adjacent statement),
stated as a top-level theorem so it can be reused without depending on instance synthesis. -/
theorem instCompleteSpace_axiom :
    CompleteSpace 𝓢(E, F) :=
  instCompleteSpaceSchwartz

namespace TemperedDistributions

/-- If a sequence in `𝓢(E, F)` is Cauchy for the canonical Schwartz metric, then it is
Cauchy for every truncated supremum-seminorm `supSeminorm k`. -/
theorem seminorm_cauchy_of_schwartzDist_cauchy
    (u : ℕ → 𝓢(E, F)) (hcauchy : ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      schwartzDist (u n) (u m) < ε)
    (k : ℕ) :
    ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      supSeminorm k (u n - u m) < ε :=
  schwartzDist_cauchy_implies_seminorm_cauchy u hcauchy k

open Filter Topology in

/-- Completeness of the Schwartz space `𝓢(E, F)` as a Mathlib `CompleteSpace` instance
(Melrose Prop. 6.7). -/
noncomputable instance instCompleteSpace : CompleteSpace 𝓢(E, F) :=
  instCompleteSpace_axiom

end TemperedDistributions
