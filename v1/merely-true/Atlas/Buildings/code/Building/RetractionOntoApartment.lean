/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.RetractionDef
import Atlas.Buildings.code.Building.RetractionProperties
import Atlas.Buildings.code.Building.UniqueRetraction

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- If an apartment $A$ contains every face of the building, then the building's
maximal chambers are also maximal in $A$. -/
lemma building_maximal_of_apt_contains_all
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
    {D : Finset V}
    (hD : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
    A.IsMaximal D := by
  constructor
  · exact h_all D hD.1
  · intro y hy hDy
    have hy_bldg : y ∈ b.toChamberComplex.toSimplicialComplex.faces :=
      b.apartmentSystem.sub A hA hy
    exact hD.2 y hy_bldg hDy

/-- Adjacency in a building transfers to adjacency in an apartment that
contains all faces of the building. -/
lemma building_adj_of_apt_contains_all
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
    {C D : Finset V}
    (hadj : b.toChamberComplex.toSimplicialComplex.Adjacent C D) :
    A.Adjacent C D := by
  obtain ⟨hC_max, hD_max, hne, F, hFC, hFD⟩ := hadj
  refine ⟨building_maximal_of_apt_contains_all b A hA h_all hC_max,
          building_maximal_of_apt_contains_all b A hA h_all hD_max,
          hne, F, ?_, ?_⟩
  · exact ⟨⟨h_all F hFC.1.1, h_all C hC_max.1, hFC.1.2.2⟩, hFC.2⟩
  · exact ⟨⟨h_all F hFD.1.1, h_all D hD_max.1, hFD.1.2.2⟩, hFD.2⟩

/-- Maximality in an apartment that contains all building faces lifts to
maximality in the building. -/
lemma apt_maximal_of_building_contains_all
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
    {D : Finset V}
    (hD : A.IsMaximal D) :
    b.toChamberComplex.toSimplicialComplex.IsMaximal D := by
  constructor
  · exact b.apartmentSystem.sub A hA hD.1
  · intro y hy hDy
    exact hD.2 y (h_all y hy) hDy

/-- Adjacency in an apartment that contains all faces of the building lifts
to adjacency in the building. -/
lemma apt_adj_of_building_contains_all
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
    {C D : Finset V}
    (hadj : A.Adjacent C D) :
    b.toChamberComplex.toSimplicialComplex.Adjacent C D := by
  obtain ⟨hC_max, hD_max, hne, F, hFC, hFD⟩ := hadj
  have hC_bldg := apt_maximal_of_building_contains_all b A hA h_all hC_max
  have hD_bldg := apt_maximal_of_building_contains_all b A hA h_all hD_max
  refine ⟨hC_bldg, hD_bldg, hne, F, ?_, ?_⟩
  · exact ⟨⟨b.apartmentSystem.sub A hA hFC.1.1,
           b.apartmentSystem.sub A hA hC_max.1, hFC.1.2.2⟩, hFC.2⟩
  · exact ⟨⟨b.apartmentSystem.sub A hA hFD.1.1,
           b.apartmentSystem.sub A hA hD_max.1, hFD.1.2.2⟩, hFD.2⟩

