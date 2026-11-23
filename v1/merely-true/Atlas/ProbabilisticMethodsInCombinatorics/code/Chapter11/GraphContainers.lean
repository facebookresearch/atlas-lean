/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph Finset

namespace GraphContainers

/-- The average degree of a finite simple graph, $\bar d(G) = 2|E(G)|/|V(G)|$. -/
noncomputable def avgDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- The partial binomial sum $\sum_{i=0}^{k} \binom{n}{i}$, bounding the number of subsets
of an $n$-element set of size at most $k$. -/
def binomialSum (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i



end GraphContainers
