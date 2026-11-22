/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Operator.Banach

namespace ClosedGraph

/-- **Closed Graph Theorem.** Let $B_1, B_2$ be two Banach spaces, and let
$T : B_1 \to B_2$ be a (not necessarily bounded) linear operator. Then
$T \in \mathcal{B}(B_1, B_2)$ if and only if the graph of $T$, defined as
$\Gamma(T) = \{(u, Tu) : u \in B_1\}$, is closed in $B_1 \times B_2$. -/
theorem closed_graph_theorem_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
    (T : V →ₗ[𝕜] W) :
    Continuous T ↔ IsClosed (T.graph : Set (V × W)) := by
  constructor
  · intro hT
    have : (T.graph : Set (V × W)) = {p : V × W | p.2 = T p.1} := by
      ext ⟨x, y⟩; simp [LinearMap.mem_graph_iff]
    rw [this]
    exact isClosed_eq continuous_snd (hT.comp continuous_fst)
  · exact T.continuous_of_isClosed_graph

end ClosedGraph
