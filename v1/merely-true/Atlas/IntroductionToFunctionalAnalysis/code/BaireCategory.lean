/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.Basic

namespace BaireCategory

open Set Topology

/-- **Baire Category Theorem.** Let $M$ be a (nonempty) complete metric space, and let
$\{C_n\}_{n \in \mathbb{N}}$ be a collection of closed subsets of $M$ such that
$M = \bigcup_{n \in \mathbb{N}} C_n$. Then at least one of the $C_n$ has nonempty interior,
i.e. contains an open ball $B(x, r) = \{y \in M : d(x, y) < r\}$. -/
theorem baire_category_theorem
    {M : Type*} [MetricSpace M] [CompleteSpace M] [Nonempty M]
    {C : ℕ → Set M} (hc : ∀ n, IsClosed (C n)) (hU : ⋃ n, C n = univ) :
    ∃ n, (interior (C n)).Nonempty :=
  nonempty_interior_of_iUnion_of_closed hc hU

end BaireCategory
