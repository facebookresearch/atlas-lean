/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- An abstract local ring at a point $P$ of a curve $C/k$ with function field $K = k(C)$:
the ring of regular functions $\mathcal{O}_P = \{f \in k(C) : f(P) \neq \infty\}$ presented
as a valuation subring of $K$ whose valuation is nontrivial and trivial on the constants $k$
(Definition 23.3). -/
structure LocalRingAtPoint (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] where
  toValuationSubring : ValuationSubring K
  valuation_nontrivial : toValuationSubring.valuation.IsNontrivial
  valuation_trivial_on_k : ∀ (a : k), a ≠ 0 →
    toValuationSubring.valuation (algebraMap k K a) = 1

namespace LocalRingAtPoint

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
variable (P : LocalRingAtPoint k K)

/-- The local ring at a point is a local ring (it has a unique maximal ideal). -/
instance instIsLocalRing : IsLocalRing P.toValuationSubring :=
  P.toValuationSubring.isLocalRing


/-- The unique maximal ideal $\mathfrak{m}_P = \{f \in \mathcal{O}_P : f(P) = 0\}$ of the
local ring at $P$. -/
noncomputable def maximalIdeal : Ideal P.toValuationSubring :=
  IsLocalRing.maximalIdeal P.toValuationSubring

/-- An element $u \in \mathcal{O}_P$ is a uniformizer at $P$ if it generates the maximal
ideal $\mathfrak{m}_P = (u)$ (Definition 23.3). -/
def IsUniformizerAt (u : P.toValuationSubring) : Prop :=
  P.maximalIdeal = Ideal.span {u}

/-- A rational function $g \in K$ is regular at $P$ if it lies in the local ring $\mathcal{O}_P$. -/
def IsRegularAt (g : K) : Prop :=
  g ∈ P.toValuationSubring

/-- Regularity at $P$ unfolds to membership in the local ring. -/
@[simp]
theorem isRegularAt_iff (g : K) : P.IsRegularAt g ↔ g ∈ P.toValuationSubring :=
  Iff.rfl

/-- Constants from $k$ are regular at every point: the image of $k$ lies in $\mathcal{O}_P$. -/
lemma algebraMap_mem (a : k) : algebraMap k K a ∈ P.toValuationSubring := by
  by_cases ha : a = 0
  · subst ha; simp [map_zero, P.toValuationSubring.zero_mem]
  · rw [← P.toValuationSubring.valuation_le_one_iff]
    rw [P.valuation_trivial_on_k a ha]

end LocalRingAtPoint

/-- An element $u$ of a local ring is a uniformizer if it generates the maximal ideal. -/
def IsUniformizer {R : Type*} [CommRing R] [IsLocalRing R] (u : R) : Prop :=
  IsLocalRing.maximalIdeal R = Ideal.span {u}
