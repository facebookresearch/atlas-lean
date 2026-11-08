/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.LinkBuilding

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- Left-cancellation for finite unions disjoint from $\sigma$: if $\sigma \cup C = \sigma \cup D$
with both $C$ and $D$ disjoint from $\sigma$, then $C = D$. -/
lemma finset_union_left_cancel {σ C D : Finset V}
    (hC_disj : Disjoint σ C) (hD_disj : Disjoint σ D)
    (h_eq : σ ∪ C = σ ∪ D) : C = D := by
  ext v
  constructor
  · intro hv
    have hv_in : v ∈ σ ∪ D := h_eq ▸ Finset.mem_union_right σ hv
    exact (Finset.mem_union.mp hv_in).elim
      (fun h => absurd h (Finset.disjoint_right.mp hC_disj hv)) id
  · intro hv
    have hv_in : v ∈ σ ∪ C := h_eq.symm ▸ Finset.mem_union_right σ hv
    exact (Finset.mem_union.mp hv_in).elim
      (fun h => absurd h (Finset.disjoint_right.mp hD_disj hv)) id
