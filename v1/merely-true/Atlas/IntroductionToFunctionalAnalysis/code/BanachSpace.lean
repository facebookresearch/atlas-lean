/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace BanachSpace

/-- If $B_1, B_2$ are Banach spaces, then $B_1 \times B_2$ (with operations done entry by entry)
with norm $\|(b_1, b_2)\| = \|b_1\| + \|b_2\|$ is a Banach space. Here this is expressed as
completeness of the $L^1$ product `WithLp 1 (B₁ × B₂)`. -/
theorem prod_banach_space (B₁ B₂ : Type*) [NormedAddCommGroup B₁] [NormedAddCommGroup B₂]
    [CompleteSpace B₁] [CompleteSpace B₂] : CompleteSpace (WithLp 1 (B₁ × B₂)) :=
  inferInstance

open Finset BigOperators

variable {E : Type*} [SeminormedAddCommGroup E]

/-- If $\sum_n v_n$ is absolutely summable (i.e. $\sum_n \|v_n\|$ is summable), then the sequence
of partial sums $\left\{\sum_{i=0}^{m-1} v_i\right\}_{m=1}^{\infty}$ is Cauchy. -/
theorem cauchySeq_of_summable_norm {v : ℕ → E} (hv : Summable fun n => ‖v n‖) :
    CauchySeq fun m => ∑ i ∈ Finset.range m, v i :=
  cauchySeq_range_of_norm_bounded (hv.hasSum.tendsto_sum_nat.cauchySeq) (fun _ => le_rfl)

end BanachSpace
