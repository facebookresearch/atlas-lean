/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SimpleGraph

variable {W : Type*} {V : Type*}

/-- `H.IsMinor G` asserts that `H` is a minor of `G`: there is a family of pairwise
disjoint, nonempty, connected vertex subsets (branch sets) $\{f(w)\}_{w \in W}$ of `G`
such that whenever $w_1$ and $w_2$ are adjacent in `H`, there is an edge in `G` between
the branch sets $f(w_1)$ and $f(w_2)$. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W → Set V,
    (∀ w, (f w).Nonempty) ∧
    (∀ w, (G.induce (f w)).Connected) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (f w₁) (f w₂)) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ v₁ ∈ f w₁, ∃ v₂ ∈ f w₂, G.Adj v₁ v₂)


end SimpleGraph
