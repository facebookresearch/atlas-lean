/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

namespace SimpleGraph

/-- Decidability of adjacency in the complete bipartite graph on $V \sqcup W$. -/
instance completeBipartiteGraph.instDecidableRel (V W : Type*) [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro x y
  simp only [completeBipartiteGraph]
  exact instDecidableOr

/-- $i(G)$: the number of independent sets in a finite simple graph $G$, counting the
empty set. -/
noncomputable def numIndSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v)).card





end SimpleGraph
