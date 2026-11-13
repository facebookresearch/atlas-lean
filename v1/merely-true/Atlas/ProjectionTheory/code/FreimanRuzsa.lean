/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset Pointwise

namespace FreimanRuzsa

/-- A generalized arithmetic progression (GAP) in an abelian group $\alpha$: a base point,
a `dim`-dimensional family of step directions $v_1,\dots,v_{\dim}$, and integer lengths
$N_1,\dots,N_{\dim}$, representing the set
$\{\text{base} + n_1 v_1 + \dots + n_{\dim} v_{\dim} : 0 \le n_i < N_i\}$. -/
structure GAP (α : Type*) [AddCommGroup α] where
  dim : ℕ
  base : α
  dirs : Fin dim → α
  lengths : Fin dim → ℕ

/-- The finset of points represented by a GAP $P$: all sums
$P.\text{base} + \sum_i n_i \cdot P.\text{dirs}\,i$ for $0 \le n_i < P.\text{lengths}\,i$. -/
noncomputable def GAP.toFinset [DecidableEq α] [AddCommGroup α] (P : GAP α) : Finset α :=
  (Fintype.piFinset (fun i => Finset.range (P.lengths i))).image
    (fun n => P.base + ∑ i : Fin P.dim, (n i) • (P.dirs i))

/-- The volume of a GAP, i.e. the product $\prod_i P.\text{lengths}\,i$ of all the side
lengths. This bounds the cardinality of `P.toFinset`. -/
def GAP.volume [AddCommGroup α] (P : GAP α) : ℕ :=
  ∏ i : Fin P.dim, P.lengths i



end FreimanRuzsa
