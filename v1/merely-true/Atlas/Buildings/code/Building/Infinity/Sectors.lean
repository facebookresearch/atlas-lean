/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineMetric
import Atlas.Buildings.code.Building.Spherical
import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.UniqueRetraction
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- A *sector* in a Euclidean apartment $A$ of a building: a base vertex together with
a nonempty vertex set inside $A$, modeling a Weyl chamber (Section 16.5). -/
structure Sector (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  baseVertex : V
  baseVertex_mem : ∃ s ∈ apartment.faces, baseVertex ∈ s
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  baseVertex_in_sector : baseVertex ∈ vertices
  nonempty : vertices.Nonempty

/-- Two sectors $S_1, S_2$ point in the same direction iff they have subsectors
$T_1 \subseteq S_1$ and $T_2 \subseteq S_2$ with $T_1.\text{vertices} = T_2.\text{vertices}$
— the parallelism relation underlying $X_\infty$ (Section 16.6). -/
def Sector.SameDirection (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.vertices = T₂.vertices

/-- A *direction*: the equivalence class of a sector under `SameDirection`, i.e. a
point of $X_\infty$ at the sector level. -/
def Sector.Direction (b : Building V) :=
  Quot (Sector.SameDirection b)

/-- $S'$ is a *subsector* of $S$: $S'.\text{vertices} \subseteq S.\text{vertices}$
and the two sectors share a direction. -/
def Sector.Subsector (b : Building V) (S' S : Sector b) : Prop :=
  S'.vertices ⊆ S.vertices ∧ Sector.SameDirection b S' S

/-- $S_1$ and $S_2$ are *opposite* sectors: same apartment, and they contain
subsectors sharing a common base vertex. -/
def Sector.IsOpposite (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  S₁.apartment = S₂.apartment ∧
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.baseVertex = T₂.baseVertex

/-- A *geodesic ray* in the affine building: a map $ℕ → V$ that is an isometric
embedding for the building distance, $d(\rho(m), \rho(n)) = |m - n|$. -/
structure GeodesicRay (b : Building V) (md : ApartmentMetricData b) where
  toFun : ℕ → V
  isometry : ∀ m n : ℕ, buildingDist b md (toFun m) (toFun n) = ((m : ℤ) - (n : ℤ)).natAbs

/-- Two geodesic rays $\rho_1, \rho_2$ are *parallel* if $\sup_n d(\rho_1(n),\rho_2(n)) < \infty$
(bounded Hausdorff distance). -/
def GeodesicRay.Parallel (b : Building V) (md : ApartmentMetricData b)
    (ρ₁ ρ₂ : GeodesicRay b md) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, buildingDist b md (ρ₁.toFun n) (ρ₂.toFun n) ≤ C

/-- A *point at infinity* of the affine building: an equivalence class of
geodesic rays under parallelism. -/
def PointAtInfinity (b : Building V) (md : ApartmentMetricData b) :=
  Quot (GeodesicRay.Parallel b md)

/-- $S_\infty$: the set of points at infinity represented by geodesic rays that
remain entirely inside the sector $S$. -/
def Sector.pointsAtInfinity {b : Building V}
    (S : Sector b) (md : ApartmentMetricData b) :
    Set (PointAtInfinity b md) :=
  { p | ∃ (ρ : GeodesicRay b md), (∀ n, ρ.toFun n ∈ S.vertices) ∧
    p = Quot.mk (GeodesicRay.Parallel b md) ρ }

/-- Predicate: vertex $v$ belongs to some face of apartment $A$. -/
def VertexInApartment (A : SimplicialComplex V) (v : V) : Prop :=
  ∃ s ∈ A.faces, v ∈ s

/-- Predicate: every vertex of $S$ lies in some face of apartment $A$. -/
def SetInApartment (A : SimplicialComplex V) (S : Set V) : Prop :=
  ∀ v ∈ S, VertexInApartment A v

/-- Every face of an apartment extends to a maximal face (chamber) of that apartment. -/
theorem apt_face_extends_to_chamber_of_building (b : Building V) :
    ∀ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D := by
  intro A hA_mem s hs_face

  obtain ⟨_B_idx, _M, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA_mem

  have hs_cc : s ∈ cc.faces := hcc_eq ▸ hs_face
  obtain ⟨C, hC_max, hs_sub_C⟩ := cc.exists_maximal s hs_cc

  have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max
  exact ⟨C, hC_max_A.1, hC_max_A, hs_sub_C⟩

/-- Auxiliary axiomatic data needed to manipulate sectors: every apartment face
extends to a chamber, and the chamber containing a sector vertex is contained
in the sector. -/
structure SectorInfrastructure (_b : Building V) where
  apt_face_extends_to_chamber :
    ∀ (A : SimplicialComplex V), A ∈ _b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D
  sector_chamber_closed :
    ∀ (S : Sector _b) (D : Finset V),
      D ∈ S.apartment.faces → S.apartment.IsMaximal D →
      (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices

/-- Convenience constructor for `SectorInfrastructure` using the building-level
chamber extension lemma. -/
def SectorInfrastructure.mk' (b : Building V)
    (sector_chamber_closed :
      ∀ (S : Sector b) (D : Finset V),
        D ∈ S.apartment.faces → S.apartment.IsMaximal D →
        (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices) :
    SectorInfrastructure b :=
  { apt_face_extends_to_chamber := apt_face_extends_to_chamber_of_building b
    sector_chamber_closed := sector_chamber_closed }

/-- Every vertex of a sector lies in a chamber of the apartment contained entirely
in the sector. -/
theorem SectorInfrastructure.sector_chamber_cover
    {b : Building V} (si : SectorInfrastructure b) :
    ∀ (S : Sector b), ∀ v ∈ S.vertices,
      ∃ D ∈ S.apartment.faces,
        S.apartment.IsMaximal D ∧ v ∈ D ∧ ∀ w ∈ D, w ∈ S.vertices := by
  intro S v hv

  obtain ⟨s, hs_face, hv_in_s⟩ := S.vertices_in_apartment v hv

  obtain ⟨D, hD_face, hD_max, hs_sub_D⟩ :=
    si.apt_face_extends_to_chamber S.apartment S.apartment_mem s hs_face

  have hv_in_D : v ∈ D := hs_sub_D hv_in_s

  have hD_in_S : ∀ w ∈ D, w ∈ S.vertices :=
    si.sector_chamber_closed S D hD_face hD_max ⟨v, hv_in_D, hv⟩
  exact ⟨D, hD_face, hD_max, hv_in_D, hD_in_S⟩

/-- Every sector contains at least one chamber (maximal face) of its apartment. -/
theorem SectorInfrastructure.sector_has_chamber
    {b : Building V} (si : SectorInfrastructure b) :
    ∀ (S : Sector b),
      ∃ C, C ∈ S.apartment.faces ∧ S.apartment.IsMaximal C ∧
        ∀ v ∈ C, v ∈ S.vertices := by
  intro S
  obtain ⟨v, hv⟩ := S.nonempty
  obtain ⟨D, hD_face, hD_max, _, hD_in_S⟩ := si.sector_chamber_cover S v hv
  exact ⟨D, hD_face, hD_max, hD_in_S⟩

/-- For any vertex $v \in S$, the sector based at $v$ with the same vertex set is a
subsector of $S$ with the same apartment. -/
theorem SectorInfrastructure.cone_vertex_subsector
    {b : Building V} (_si : SectorInfrastructure b)
    (S : Sector b) (v : V) (hv : v ∈ S.vertices) :
    ∃ (S' : Sector b),
      S'.apartment = S.apartment ∧
      S'.baseVertex = v ∧
      S'.vertices ⊆ S.vertices := by

  refine ⟨⟨S.apartment, S.apartment_mem, v,
    S.vertices_in_apartment v hv, S.vertices, S.vertices_in_apartment,
    hv, S.nonempty⟩, rfl, rfl, Set.Subset.refl _⟩

/-- Two apartments sharing a chamber $C$ admit an isomorphism that fixes $C$ pointwise. -/
theorem SectorInfrastructure.iso_from_shared_chamber
    {b : Building V} (_si : SectorInfrastructure b)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : A.IsMaximal C) :
    ∃ φ : SimplicialMap A A', ∀ v ∈ C, φ.toFun v = v := by

  obtain ⟨φ, _, hfix_C⟩ :=
    b.apartmentSystem.iso_exists A hA A' hA' C hC_A hC_A' C hC_max hC_A'
  exact ⟨φ, hfix_C⟩

/-- Reflexivity of `SameDirection`. -/
theorem Sector.SameDirection.refl (b : Building V) (S : Sector b) :
    Sector.SameDirection b S S :=
  ⟨S, S, Set.Subset.refl _, Set.Subset.refl _, rfl⟩

/-- Symmetry of `SameDirection`. -/
theorem Sector.SameDirection.symm {b : Building V} {S₁ S₂ : Sector b}
    (h : Sector.SameDirection b S₁ S₂) :
    Sector.SameDirection b S₂ S₁ := by
  obtain ⟨T₁, T₂, hT₁, hT₂, hTeq⟩ := h
  exact ⟨T₂, T₁, hT₂, hT₁, hTeq.symm⟩

/-- Every sector is a subsector of itself. -/
theorem Sector.Subsector.refl (b : Building V) (S : Sector b) :
    Sector.Subsector b S S :=
  ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩

end AffineBuilding
