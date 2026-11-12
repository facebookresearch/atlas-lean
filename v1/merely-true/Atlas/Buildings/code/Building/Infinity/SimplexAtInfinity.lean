/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.Sectors

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- An ideal simplex of the building at infinity: a nonempty set of points at infinity
that arises as a subset of $S_\infty$ for some sector $S$ (Section 16.8). -/
structure SimplexAtInfinity (b : Building V) (md : ApartmentMetricData b) where
  points : Set (PointAtInfinity b md)
  from_sector : ∃ (S : Sector b), points ⊆ S.pointsAtInfinity md
  nonempty : points.Nonempty

/-- An apartment $A_\infty$ of the building at infinity: the boundary of a Euclidean
apartment $A \subseteq X$, packaged with its ideal simplices (Section 16.8). -/
structure ApartmentAtInfinity (b : Building V) (md : ApartmentMetricData b) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  simplices : Set (SimplexAtInfinity b md)
  simplices_from_apartment : ∀ σ ∈ simplices,
    ∃ (S : Sector b), S.apartment = apartment

/-- The building at infinity $X_\infty$ of an affine building $X$: ideal simplices
together with apartments $A_\infty$, satisfying the building axiom that any two
simplices lie in a common apartment (Sections 16.8–16.9). -/
structure BuildingAtInfinity (b : Building V) (md : ApartmentMetricData b) where
  simplices : Set (SimplexAtInfinity b md)
  apartments : Set (ApartmentAtInfinity b md)
  apartment_simplices_mem : ∀ A ∈ apartments, A.simplices ⊆ simplices
  contains_pair : ∀ σ₁ ∈ simplices, ∀ σ₂ ∈ simplices,
    ∃ A ∈ apartments, σ₁ ∈ A.simplices ∧ σ₂ ∈ A.simplices

/-- The building at infinity is *spherical*: each apartment $A_\infty$ has finitely
many simplices and at least one apartment exists (Section 16.10). -/
def BuildingAtInfinity.IsSpherical (b : Building V) (md : ApartmentMetricData b)
    (Binf : BuildingAtInfinity b md) : Prop :=

  (∀ A ∈ Binf.apartments, Set.Finite A.simplices) ∧


  Binf.apartments.Nonempty

end AffineBuilding
