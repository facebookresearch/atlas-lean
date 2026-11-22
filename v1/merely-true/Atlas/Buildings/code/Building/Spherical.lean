/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Mathlib.Data.List.Chain

variable {V : Type*} [DecidableEq V]

/-- The set of chambers (maximal faces) of a simplicial complex $K$. -/
def SimplicialComplex.chambers (K : SimplicialComplex V) : Set (Finset V) :=
  { C | K.IsMaximal C }

/-- A building is *spherical* if every apartment has finitely many faces
(equivalently, finite diameter). -/
def Building.IsSpherical (b : Building V) : Prop :=
  ∀ A ∈ b.apartmentSystem.apartments,
    Set.Finite A.faces

/-- The *diameter* of a simplicial complex: the supremum of gallery distances
between pairs of chambers. -/
noncomputable def SimplicialComplex.diameter (K : SimplicialComplex V) : ℕ :=
  sSup { n | ∃ C D, K.IsMaximal C ∧ K.IsMaximal D ∧ galleryDist K C D = n }

/-- Two chambers $C, D$ of $K$ are *opposite* if both are chambers and their
gallery distance is maximal among all pairs of chambers in $K$. -/
def AreOpposite (K : SimplicialComplex V) (C D : Finset V) : Prop :=
  K.IsMaximal C ∧ K.IsMaximal D ∧
  ∀ C' D', K.IsMaximal C' → K.IsMaximal D' →
    galleryDist K C' D' ≤ galleryDist K C D

section AreOppositeTheorems

variable {K : SimplicialComplex V}

/-- The opposition relation between chambers is symmetric. -/
theorem areOpposite_symm {C D : Finset V}
    (h : AreOpposite K C D) : AreOpposite K D C := by
  obtain ⟨hC, hD, hmax⟩ := h
  refine ⟨hD, hC, fun C' D' hC' hD' => ?_⟩
  rw [galleryDist_comm K D C]
  exact hmax C' D' hC' hD'

end AreOppositeTheorems

section ChamberMembership

/-- Membership in `K.chambers` is the same as being a maximal face. -/
theorem SimplicialComplex.mem_chambers_iff (K : SimplicialComplex V) (C : Finset V) :
    C ∈ K.chambers ↔ K.IsMaximal C :=
  Iff.rfl

/-- Every chamber is a face. -/
theorem SimplicialComplex.chambers_subset_faces (K : SimplicialComplex V) :
    K.chambers ⊆ K.faces := by
  intro C hC
  exact ((K.mem_chambers_iff C).mp hC).1

end ChamberMembership

section SphericalTheorems

/-- In a spherical building, each apartment has finitely many chambers. -/
theorem Building.IsSpherical.finite_chambers (b : Building V) (hsph : b.IsSpherical)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite (A.chambers) := by
  apply Set.Finite.subset (hsph A hA)
  exact A.chambers_subset_faces

end SphericalTheorems
