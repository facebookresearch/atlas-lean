/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.Instances.Real.Lemmas
set_option maxHeartbeats 800000

noncomputable section

namespace SharpThresholdColorability

open Filter Topology SimpleGraph Finset

/-- Number of potential edges in a simple graph on $n$ vertices, i.e. $\binom{n}{2}$. -/
def numPossibleEdges (n : ℕ) : ℕ := n.choose 2

open Classical in
/-- Erdős-Rényi weight $p^{|E(G)|} (1-p)^{\binom{n}{2} - |E(G)|}$ assigned to a labeled
graph $G$ on $\{0, \dots, n-1\}$ in $G(n,p)$. -/
def erdosRenyiWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ G.edgeFinset.card * (1 - p) ^ (numPossibleEdges n - G.edgeFinset.card)

open Classical in
/-- Probability that $G(n,p)$ is $k$-colorable, computed as the Erdős-Rényi-weighted count
of labeled $k$-colorable simple graphs on $\{0, \dots, n-1\}$. -/
def probColorable (n : ℕ) (k : ℕ) (p : ℝ) : ℝ :=
  ∑ G ∈ (Finset.univ : Finset (SimpleGraph (Fin n))).filter (fun G => G.Colorable k),
    erdosRenyiWeight n p G


end SharpThresholdColorability
