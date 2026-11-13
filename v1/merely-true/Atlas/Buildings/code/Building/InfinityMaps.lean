/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.InfinityConstruction
import Atlas.Buildings.code.Building.Labels
import Mathlib.Data.NNReal.Basic

set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- A simplicial automorphism of a building $\mathcal{B}$: a bijection on
vertices that maps faces to faces and apartments to apartments. -/
structure IsSimplicialAutomorphism (b : Building V) (f : V → V) where
  maps_faces : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s.image f ∈ b.toChamberComplex.toSimplicialComplex.faces
  bijective : Function.Bijective f
  maps_apartments : ∀ A ∈ b.apartmentSystem.apartments,
    ∃ A' ∈ b.apartmentSystem.apartments,
      ∀ s ∈ A.faces, s.image f ∈ A'.faces

/-- An isometry of the building's vertex set with respect to the apartment
metric: a vertex map $\varphi$ preserving the building distance. -/
structure BuildingIsometry (b : Building V) (md : ApartmentMetricData b) where
  toFun : V → V
  isometry : ∀ v w : V, buildingDist b md (toFun v) (toFun w) =
    buildingDist b md v w

/-- The pushforward of a geodesic ray $\rho$ under a building isometry
$\varphi$ is the composite ray $\varphi \circ \rho$. -/
noncomputable def BuildingIsometry.pushforwardRay
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : GeodesicRay b md) :
    GeodesicRay b md where
  toFun := φ.toFun ∘ ρ.toFun
  isometry := fun m n => by
    simp only [Function.comp]
    rw [φ.isometry]
    exact ρ.isometry m n

/-- A building isometry preserves parallelism of geodesic rays:
$\rho_1 \parallel \rho_2 \implies \varphi \rho_1 \parallel \varphi \rho_2$. -/
theorem isometry_preserves_parallelism
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ₁ ρ₂ : GeodesicRay b md)
    (h : GeodesicRay.Parallel b md ρ₁ ρ₂) :
    GeodesicRay.Parallel b md (φ.pushforwardRay ρ₁) (φ.pushforwardRay ρ₂) := by
  obtain ⟨C, hC_pos, hC⟩ := h
  exact ⟨C, hC_pos, fun n => by
    simp only [BuildingIsometry.pushforwardRay, Function.comp]
    rw [φ.isometry]
    exact hC n⟩

/-- The origin $\rho(0)$ of a geodesic ray. -/
def GeodesicRay.origin {b : Building V} {md : ApartmentMetricData b}
    (ρ : GeodesicRay b md) : V :=
  ρ.toFun 0

/-- The point at infinity of a geodesic ray $\rho$, as the parallelism class of $\rho$. -/
def GeodesicRay.pointAtInfinity {b : Building V} {md : ApartmentMetricData b}
    (ρ : GeodesicRay b md) : PointAtInfinity b md :=
  Quot.mk (GeodesicRay.Parallel b md) ρ

/-- The origin of $\varphi \rho$ is $\varphi$ applied to the origin of $\rho$. -/
theorem BuildingIsometry.pushforwardRay_origin
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : GeodesicRay b md) :
    (φ.pushforwardRay ρ).origin = φ.toFun ρ.origin := by
  rfl

/-- A geodesic ray parametrised by $\mathbb{R}_{\geq 0}$ rather than $\mathbb{N}$:
a map $\rho : \mathbb{R}_{\geq 0} \to V$ that is an isometry onto its image. -/
structure ContinuousGeodesicRay (b : Building V) (md : ApartmentMetricData b) where
  toFun : NNReal → V
  isometry : ∀ s t : NNReal,
    buildingDist b md (toFun s) (toFun t) = |(s : ℝ) - (t : ℝ)|

/-- Two continuous geodesic rays are parallel iff they stay within a uniform
distance $C \geq 0$ of each other at all times $t \geq 0$. -/
def ContinuousGeodesicRay.Parallel (b : Building V) (md : ApartmentMetricData b)
    (ρ₁ ρ₂ : ContinuousGeodesicRay b md) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal,
    buildingDist b md (ρ₁.toFun t) (ρ₂.toFun t) ≤ C

/-- Points at infinity in the continuous parametrisation: parallelism classes
of continuous geodesic rays. -/
def ContinuousPointAtInfinity (b : Building V) (md : ApartmentMetricData b) :=
  Quot (ContinuousGeodesicRay.Parallel b md)

/-- Pushforward of a continuous geodesic ray under a building isometry. -/
noncomputable def BuildingIsometry.pushforwardContinuousRay
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : ContinuousGeodesicRay b md) :
    ContinuousGeodesicRay b md where
  toFun := φ.toFun ∘ ρ.toFun
  isometry := fun s t => by
    simp only [Function.comp]
    rw [φ.isometry]
    exact ρ.isometry s t

/-- A building isometry preserves parallelism of continuous geodesic rays. -/
theorem isometry_preserves_parallelism_continuous
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ₁ ρ₂ : ContinuousGeodesicRay b md)
    (h : ContinuousGeodesicRay.Parallel b md ρ₁ ρ₂) :
    ContinuousGeodesicRay.Parallel b md
      (φ.pushforwardContinuousRay ρ₁) (φ.pushforwardContinuousRay ρ₂) := by
  obtain ⟨C, hC_pos, hC⟩ := h
  exact ⟨C, hC_pos, fun t => by
    simp only [BuildingIsometry.pushforwardContinuousRay, Function.comp]
    rw [φ.isometry]
    exact hC t⟩

/-- The induced map $\varphi_\infty$ on continuous points at infinity:
descended from the pushforward of rays through the parallelism quotient. -/
noncomputable def BuildingIsometry.inducedMapInfinityCont
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) :
    ContinuousPointAtInfinity b md → ContinuousPointAtInfinity b md :=
  Quot.lift
    (fun ρ => Quot.mk (ContinuousGeodesicRay.Parallel b md)
      (φ.pushforwardContinuousRay ρ))
    (fun ρ₁ ρ₂ hpar => Quot.sound
      (isometry_preserves_parallelism_continuous φ ρ₁ ρ₂ hpar))

/-- The induced map $\varphi_\infty$ commutes with the parallelism quotient
on continuous rays. -/
theorem BuildingIsometry.inducedMapInfinityCont_mk
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ : ContinuousGeodesicRay b md) :
    φ.inducedMapInfinityCont (Quot.mk _ ρ) =
      Quot.mk (ContinuousGeodesicRay.Parallel b md)
        (φ.pushforwardContinuousRay ρ) := by
  rfl

/-- The origin $\rho(0)$ of a continuous geodesic ray. -/
def ContinuousGeodesicRay.origin {b : Building V} {md : ApartmentMetricData b}
    (ρ : ContinuousGeodesicRay b md) : V :=
  ρ.toFun 0

/-- The point at infinity of a continuous geodesic ray. -/
def ContinuousGeodesicRay.pointAtInfinity {b : Building V} {md : ApartmentMetricData b}
    (ρ : ContinuousGeodesicRay b md) : ContinuousPointAtInfinity b md :=
  Quot.mk (ContinuousGeodesicRay.Parallel b md) ρ

/-- The origin formula for the pushforward of a continuous ray. -/
theorem BuildingIsometry.pushforwardContinuousRay_origin
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : ContinuousGeodesicRay b md) :
    (φ.pushforwardContinuousRay ρ).origin = φ.toFun ρ.origin := by
  rfl

/-- The point-at-infinity formula for the pushforward of a continuous ray. -/
theorem BuildingIsometry.pushforwardContinuousRay_pointAtInfinity
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : ContinuousGeodesicRay b md) :
    (φ.pushforwardContinuousRay ρ).pointAtInfinity =
      φ.inducedMapInfinityCont ρ.pointAtInfinity := by
  simp only [ContinuousGeodesicRay.pointAtInfinity, BuildingIsometry.inducedMapInfinityCont_mk]

/-- Combined formula: pushing forward a continuous ray transports both its
origin and its point at infinity. -/
theorem isometry_ray_formula_cont
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : ContinuousGeodesicRay b md) :
    (φ.pushforwardContinuousRay ρ).origin = φ.toFun ρ.origin ∧
    (φ.pushforwardContinuousRay ρ).pointAtInfinity =
      φ.inducedMapInfinityCont ρ.pointAtInfinity :=
  ⟨φ.pushforwardContinuousRay_origin ρ, φ.pushforwardContinuousRay_pointAtInfinity ρ⟩

/-- The induced map $\varphi_\infty$ on points at infinity (discrete
parametrisation) descending from ray pushforward. -/
noncomputable def BuildingIsometry.inducedMapInfinity
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) :
    PointAtInfinity b md → PointAtInfinity b md :=
  Quot.lift
    (fun ρ => Quot.mk (GeodesicRay.Parallel b md) (φ.pushforwardRay ρ))
    (fun ρ₁ ρ₂ hpar => Quot.sound (isometry_preserves_parallelism φ ρ₁ ρ₂ hpar))

/-- The induced map $\varphi_\infty$ commutes with the parallelism quotient on rays. -/
theorem BuildingIsometry.inducedMapInfinity_mk
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ : GeodesicRay b md) :
    φ.inducedMapInfinity (Quot.mk _ ρ) =
      Quot.mk (GeodesicRay.Parallel b md) (φ.pushforwardRay ρ) := by
  rfl

/-- Pushing forward a ray transports its point at infinity through $\varphi_\infty$. -/
theorem BuildingIsometry.pushforwardRay_pointAtInfinity
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : GeodesicRay b md) :
    (φ.pushforwardRay ρ).pointAtInfinity =
      φ.inducedMapInfinity ρ.pointAtInfinity := by
  simp only [GeodesicRay.pointAtInfinity, BuildingIsometry.inducedMapInfinity_mk]

/-- If a simplicial automorphism $f$ sends a sector's apartment into an
apartment $A'$, then the image $f(S)$ is again a sector with apartment $A'$. -/
theorem automorphism_maps_sectors_apartment
    {V : Type} [DecidableEq V]
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (S : Sector b) (A' : SimplicialComplex V)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (h_maps : ∀ s ∈ S.apartment.faces, s.image f ∈ A'.faces) :
    ∃ (S' : Sector b), S'.vertices = f '' S.vertices ∧ S'.apartment = A' := by


  obtain ⟨s_base, hs_base_face, h_bv_in_s⟩ := S.baseVertex_mem
  have h_img_base_face : s_base.image f ∈ A'.faces := h_maps s_base hs_base_face
  have h_fbv_in_img : f S.baseVertex ∈ s_base.image f := Finset.mem_image_of_mem f h_bv_in_s

  have h_singleton_face : {f S.baseVertex} ∈ A'.faces :=
    A'.down_closed h_img_base_face (Finset.singleton_subset_iff.mpr h_fbv_in_img)
      (Finset.singleton_nonempty _)

  have h_verts_in_apt : ∀ v ∈ f '' S.vertices, ∃ s ∈ A'.faces, v ∈ s := by
    intro v hv
    obtain ⟨u, hu_in, rfl⟩ := hv
    obtain ⟨s, hs_face, hu_in_s⟩ := S.vertices_in_apartment u hu_in
    exact ⟨s.image f, h_maps s hs_face, Finset.mem_image_of_mem f hu_in_s⟩

  have h_fbv_in_verts : f S.baseVertex ∈ f '' S.vertices :=
    ⟨S.baseVertex, S.baseVertex_in_sector, rfl⟩


  have h_sub : IsSubcomplex A' b.toChamberComplex.toSimplicialComplex :=
    b.apartmentSystem.sub A' hA'

  refine ⟨⟨A', hA', f S.baseVertex,
    ⟨s_base.image f, h_img_base_face, h_fbv_in_img⟩,
    f '' S.vertices, h_verts_in_apt, h_fbv_in_verts,
    Set.Nonempty.image f S.nonempty⟩, rfl, rfl⟩

/-- A simplicial automorphism sends every sector to another sector (in some
apartment of the building's system). -/
theorem automorphism_maps_sectors
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (S : Sector b) :
    ∃ (S' : Sector b), S'.vertices = f '' S.vertices := by
  obtain ⟨A', hA', hA'_faces⟩ := hf.maps_apartments S.apartment S.apartment_mem
  obtain ⟨S', hS', _⟩ := automorphism_maps_sectors_apartment f hf S A' hA'
    (fun s hs => hA'_faces s hs)
  exact ⟨S', hS'⟩

/-- An injective face-preserving map with a face-preserving two-sided inverse
sends maximal faces to maximal faces. -/
lemma injective_face_map_maximal
    {V : Type} [DecidableEq V]

    {K : SimplicialComplex V}
    (h : V → V) (h_inj : Function.Injective h)
    (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
    (h_inv : V → V) (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
    (h_inv_left : ∀ v, h_inv (h v) = v)
    (h_right : ∀ v, h (h_inv v) = v)
    (C : Finset V) (hC : K.IsMaximal C) :
    K.IsMaximal (C.image h) := by
  refine ⟨h_faces C hC.1, ?_⟩
  intro D hD hCD
  have h_Cinv : (C.image h).image h_inv = C := by
    rw [Finset.image_image]
    have : h_inv ∘ h = id := funext h_inv_left
    rw [this, Finset.image_id]
  have h_sub : C ⊆ D.image h_inv := by
    rw [← h_Cinv]; exact Finset.image_subset_image hCD
  have hD_inv_face : D.image h_inv ∈ K.faces := h_inv_faces D hD
  have hmax := hC.2 (D.image h_inv) hD_inv_face h_sub
  rw [hmax, Finset.image_image]
  have : h ∘ h_inv = id := funext h_right
  rw [this, Finset.image_id]

/-- Such a bijective face-preserving map also preserves chamber adjacency. -/
lemma injective_face_map_adjacent
    {V : Type} [DecidableEq V]
    {K : SimplicialComplex V}
    (h : V → V) (h_inj : Function.Injective h)
    (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
    (h_inv : V → V) (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
    (h_inv_left : ∀ v, h_inv (h v) = v)
    (h_right : ∀ v, h (h_inv v) = v)
    (C D : Finset V) (hadj : K.Adjacent C D) :
    K.Adjacent (C.image h) (D.image h) := by
  obtain ⟨hC_max, hD_max, hCD_ne, F, hF_C, hF_D⟩ := hadj
  refine ⟨injective_face_map_maximal h h_inj h_faces h_inv h_inv_faces h_inv_left h_right C hC_max,
          injective_face_map_maximal h h_inj h_faces h_inv h_inv_faces h_inv_left h_right D hD_max,
          ?_, F.image h, ?_, ?_⟩
  · intro heq; exact hCD_ne ((Finset.image_injective h_inj).eq_iff.mp heq)
  · constructor
    · exact ⟨h_faces F hF_C.1.1, h_faces C hC_max.1, Finset.image_subset_image hF_C.1.2.2⟩
    · rw [← Finset.image_sdiff_of_injOn (Set.injOn_of_injective h_inj) hF_C.1.2.2]
      rw [Finset.card_image_of_injective _ h_inj]
      exact hF_C.2
  · constructor
    · exact ⟨h_faces F hF_D.1.1, h_faces D hD_max.1, Finset.image_subset_image hF_D.1.2.2⟩
    · rw [← Finset.image_sdiff_of_injOn (Set.injOn_of_injective h_inj) hF_D.1.2.2]
      rw [Finset.card_image_of_injective _ h_inj]
      exact hF_D.2









/-- A building isometry preserves a chamber-complex labelling if the label
of each face is invariant under $\varphi$. -/
def BuildingIsometry.IsLabelPreserving
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    lab.labelMap (s.image φ.toFun) = lab.labelMap s

/-- A simplicial automorphism preserves a labelling iff every face has the
same label as its image. -/
def IsLabelPreservingAuto (b : Building V) (f : V → V)
    {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    lab.labelMap (s.image f) = lab.labelMap s

/-- A labelling of $X_\infty$: a label-finset map on simplices at infinity
that is strictly monotone with respect to the face relation. -/
structure InfinityLabelling
    {V : Type} [DecidableEq V]
    {b : Building V} {md : ApartmentMetricData b}
    (L_inf : Type*) [DecidableEq L_inf] where
  labelMap : SimplexAtInfinity b md → Finset L_inf
  label_strictMono : ∀ (σ τ : SimplexAtInfinity b md),
    SimplexAtInfinity.IsFace b md σ τ → σ ≠ τ →
    labelMap σ ⊂ labelMap τ


/-- A map $F$ on $X_\infty$ preserves a labelling iff each simplex has the
same label as its image. -/
def InfinityLabelling.IsPreservedBy
    {V : Type} [DecidableEq V]
    {b : Building V} {md : ApartmentMetricData b}
    {L_inf : Type*} [DecidableEq L_inf]
    (lab : InfinityLabelling (b := b) (md := md) L_inf)
    (F : SimplexAtInfinity b md → SimplexAtInfinity b md) : Prop :=
  ∀ σ : SimplexAtInfinity b md, lab.labelMap (F σ) = lab.labelMap σ


/-- If $f$ stabilises an apartment $A$ and $S$ is a sector in $A$, then
$f(S)$ is again a sector inside $A$. -/
theorem stabilizer_maps_sectors_to_same_apartment
    {V : Type} [DecidableEq V]
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (h_stab : ∀ s ∈ A.faces, s.image f ∈ A.faces)
    (S : Sector b) (hS : S.apartment = A) :
    ∃ (S' : Sector b), S'.vertices = f '' S.vertices ∧ S'.apartment = A := by
  have h_maps : ∀ s ∈ S.apartment.faces, s.image f ∈ A.faces := by
    intro s hs; exact h_stab s (by rw [hS] at hs; exact hs)
  exact automorphism_maps_sectors_apartment f hf S A hA h_maps



end AffineBuilding
