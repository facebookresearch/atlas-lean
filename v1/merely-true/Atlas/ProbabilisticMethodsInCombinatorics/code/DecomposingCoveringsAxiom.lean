/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open Set Metric

namespace DecomposingCoverings

/-- Three-dimensional Euclidean space $\mathbb{R}^3$, the ambient space for the
Mani-Levitska–Pach problem on coverings by unit balls. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Indices of the unit balls that cover a point $x \in \mathbb{R}^3$:
$\{i : x \in B(\text{center}_i, 1)\}$. -/
def coveringSet {ι : Type*} (center : ι → E3) (x : E3) : Set ι :=
  {i | x ∈ Metric.ball (center i) 1}

/-- `IsKFoldCovering center k` records that a family of unit balls with centres `center`
is a locally finite $k$-fold covering of $\mathbb{R}^3$: every point is covered at least
$k$ times and only by finitely many balls. -/
structure IsKFoldCovering {ι : Type*} (center : ι → E3) (k : ℕ) : Prop where
  cover : ∀ x : E3, k ≤ (coveringSet center x).ncard
  locallyFinite : ∀ x : E3, (coveringSet center x).Finite

/-- Multiplicity at $x$: the number of unit balls of the family covering $x$. -/
noncomputable def mult {ι : Type*} (center : ι → E3) (x : E3) : ℕ :=
  (coveringSet center x).ncard

end DecomposingCoverings

namespace DecomposingCoverings



end DecomposingCoverings
