/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

namespace HomogeneousDynamics

/-- The arithmetic lattice $SL(3, \mathbb{Z})$ viewed as a subgroup of $SL(3, \mathbb{R})$
via the canonical embedding. -/
noncomputable def SL3Z : Subgroup (SpecialLinearGroup (Fin 3) ℝ) :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ)).range

/-- The unipotent matrix $U(t) = \begin{pmatrix} 1 & t & t^2 \\ 0 & 1 & t \\ 0 & 0 & 1 \end{pmatrix}$
parameterizing the one-parameter unipotent subgroup of $SL(3, \mathbb{R})$ used in
Lindenstrauss–Mohammadi–Wang–Yang. -/
noncomputable def unipotentU (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, t, t^2; 0, 1, t; 0, 0, 1]

/-- The unipotent matrix $U(t)$ has determinant $1$. -/
lemma unipotentU_det (t : ℝ) : (unipotentU t).det = 1 := by
  simp [unipotentU, Matrix.det_fin_three]

/-- The unipotent element $U(t)$ packaged as an element of $SL(3, \mathbb{R})$ using
the determinant computation. -/
noncomputable def unipotentElem (t : ℝ) : SpecialLinearGroup (Fin 3) ℝ :=
  ⟨unipotentU t, unipotentU_det t⟩

/-- A subset `S` of a pseudometric space is `ε`-dense if every point lies within distance
`ε` of some element of `S`. -/
def IsEpsDense {X : Type*} [PseudoMetricSpace X] (S : Set X) (ε : ℝ) : Prop :=
  ∀ x : X, ∃ s ∈ S, dist x s ≤ ε

/-- The orbit segment $\{U(t) \cdot x : t \in [0, T]\}$ of a point $x$ in the homogeneous
space $SL(3,\mathbb{R}) / SL(3,\mathbb{Z})$ under the unipotent flow. -/
noncomputable def orbitSegment
    (x : SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)
    (T : ℝ) : Set (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z) :=
  (fun t => unipotentElem t • x) '' (Set.Icc 0 T)

/-- A proper homogeneous subspace of $SL(3,\mathbb{R}) / SL(3,\mathbb{Z})$: a closed proper
subset invariant under a nontrivial proper subgroup of $SL(3,\mathbb{R})$.  These are the
exceptional sets near which the unipotent orbit can fail to equidistribute. -/
structure ProperHomogeneousSubspace
    [TopologicalSpace (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)] where
  carrier : Set (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)
  isClosed : IsClosed carrier
  isProper : carrier ≠ Set.univ
  isSubgroupInvariant : ∃ H : Subgroup (SpecialLinearGroup (Fin 3) ℝ),
    H ≠ ⊤ ∧ ∀ (h : SpecialLinearGroup (Fin 3) ℝ), h ∈ H → ∀ y ∈ carrier, h • y ∈ carrier

/-- The unipotent orbit closure of `x` stays at distance at least `η` from every proper
homogeneous subspace; the diophantine condition under which LMWY proves polynomial
density of the orbit. -/
def IsOrbitFarFromProperHomogeneous
    [PseudoMetricSpace (SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z)]
    (x : SpecialLinearGroup (Fin 3) ℝ ⧸ SL3Z) (η : ℝ) : Prop :=
  ∀ Y : ProperHomogeneousSubspace,
    ∀ y ∈ closure (Set.range (fun t : ℝ => unipotentElem t • x)),
      Metric.infDist y Y.carrier ≥ η


end HomogeneousDynamics
