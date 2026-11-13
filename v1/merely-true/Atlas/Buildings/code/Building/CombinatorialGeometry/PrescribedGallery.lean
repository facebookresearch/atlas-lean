/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.Labels
import Atlas.Buildings.code.Building.Convexity
import Atlas.Buildings.code.Building.ApartmentsCoxeter
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.IsCoxeterCharacterized
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.ThinFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.WallCrossing
import Atlas.Buildings.code.Building.RetractionDef

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- A gallery $g$ is *minimal* between $C$ and $D$ if it connects them with length equal to the
gallery distance $d(C, D)$. -/
def MinimalGallery (K : SimplicialComplex V) (g : Gallery K)
    (C D : Finset V) : Prop :=
  g.Connects C D ∧ g.length = galleryDist K C D

/-- A gallery is *reduced* if it is non-stuttering and minimal. -/
def ReducedGallery (K : SimplicialComplex V) (g : Gallery K)
    (C D : Finset V) : Prop :=
  g.IsNonStuttering ∧ MinimalGallery K g C D

/-- The label-type of a building gallery $g$ under a labelling $\mathrm{lab}$. -/
def BuildingGalleryType {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (g : Gallery K.toSimplicialComplex) : List (Finset L) :=
  GalleryType K lab g

/-- Weyl distance $\delta_W(C, D) = (\varphi C)^{-1} \varphi D$ between chambers $C, D$ via a
Coxeter-group labelling $\varphi$. -/
noncomputable def WeylDistance {B_idx : Type*} [DecidableEq B_idx] [Fintype B_idx]
    (b : Building V) (ct : Building.CoxeterTypeOfBuilding b)
    (A : SimplicialComplex V) (_hA : A ∈ b.apartmentSystem.apartments)
    (φ : Finset V → ct.matrix.Group)
    (C D : Finset V) : ct.matrix.Group :=
  (φ C)⁻¹ * φ D

/-- Three characterizing properties of an apartment: being a subcomplex, being thin, and the
property that minimal galleries starting in $A$ stay in $A$. -/
structure ApartmentCharacterization (b : Building V) (A : SimplicialComplex V) : Prop where
  sub : IsSubcomplex A b.toSimplicialComplex
  thin : ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin
  minimalStaysIn : ∀ (g : Gallery b.toSimplicialComplex) (C D : Finset V),
    MinimalGallery b.toSimplicialComplex g C D →
    C ∈ A.faces → A.IsMaximal C →
    ∀ E ∈ g.chambers, E ∈ A.faces

/-- $K$ has *prescribed gallery existence* if every chamber and label-type sequence can be realized
as the gallery-type of some gallery starting at that chamber. -/
def PrescribedGalleryExistence {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L) : Prop :=
  ∀ (C : Finset V) (τ : List (Finset L)),
    K.toSimplicialComplex.IsMaximal C →
    ∃ (g : Gallery K.toSimplicialComplex),
      g.chambers.head? = some C ∧
      GalleryType K lab g = τ

/-- Hypotheses for the prescribed-gallery construction: existence of an apartment chain of any
prescribed length, and the lift of apartment adjacency to building adjacency. -/
structure PrescribedGalleryHypotheses (b : Building V) where
  apt_gallery_of_type :
    ∀ A ∈ b.apartmentSystem.apartments,
    ∀ (C : Finset V), C ∈ A.faces → A.IsMaximal C →
    ∀ (τ : List (Finset V)),
    ∃ (cs : List (Finset V)),
      cs.head? = some C ∧
      cs.length = τ.length + 1 ∧
      (∀ E ∈ cs, E ∈ A.faces) ∧
      List.IsChain A.Adjacent cs
  apt_adj_implies_bldg_adj :
    ∀ A ∈ b.apartmentSystem.apartments,
    ∀ C D : Finset V, C ∈ A.faces → D ∈ A.faces →
      A.Adjacent C D → b.toSimplicialComplex.Adjacent C D

/-- Adjacency in an apartment lifts to adjacency in the ambient building. -/
lemma apt_adj_lifts_to_bldg (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C D : Finset V) (_hC : C ∈ A.faces) (_hD : D ∈ A.faces)
    (hadj : A.Adjacent C D) : b.toSimplicialComplex.Adjacent C D := by
  obtain ⟨hCmax_A, hDmax_A, hne, F, hFC, hFD⟩ := hadj
  have hCmax_bldg := b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax_A
  have hDmax_bldg := b.apartmentSystem.maximal_in_apt_is_maximal A hA D hDmax_A
  have hFC_bldg : b.toSimplicialComplex.IsFacet F C :=
    ⟨⟨b.apartmentSystem.sub A hA hFC.1.1,
      b.apartmentSystem.sub A hA hFC.1.2.1, hFC.1.2.2⟩, hFC.2⟩
  have hFD_bldg : b.toSimplicialComplex.IsFacet F D :=
    ⟨⟨b.apartmentSystem.sub A hA hFD.1.1,
      b.apartmentSystem.sub A hA hFD.1.2.1, hFD.1.2.2⟩, hFD.2⟩
  exact ⟨hCmax_bldg, hDmax_bldg, hne, F, hFC_bldg, hFD_bldg⟩

/-- If every maximal chamber of $A$ has an adjacent chamber in $A$, one can build adjacency chains of any length starting at a given chamber. -/
lemma apt_chain_of_length (A : SimplicialComplex V)
    (h_has_adj : ∀ C, A.IsMaximal C → ∃ D, A.Adjacent C D)
    (C : Finset V) (hC : C ∈ A.faces) (hCmax : A.IsMaximal C)
    (n : ℕ) :
    ∃ (cs : List (Finset V)),
      cs.head? = some C ∧
      cs.length = n + 1 ∧
      (∀ E ∈ cs, E ∈ A.faces) ∧
      List.IsChain A.Adjacent cs := by
  induction n generalizing C with
  | zero =>
    exact ⟨[C], rfl, rfl,
      fun E hE => by simp at hE; rw [hE]; exact hC,
      List.IsChain.singleton C⟩
  | succ n ih =>

    obtain ⟨D, hAdj_CD⟩ := h_has_adj C hCmax
    have hDmax : A.IsMaximal D := hAdj_CD.2.1
    have hD : D ∈ A.faces := hDmax.1

    obtain ⟨cs_tail, hhead_tail, hlen_tail, hmem_tail, hchain_tail⟩ :=
      ih D hD hDmax

    refine ⟨C :: cs_tail, rfl, ?_, ?_, ?_⟩
    ·
      simp [hlen_tail]
    ·
      intro E hE
      simp only [List.mem_cons] at hE
      rcases hE with rfl | hE
      · exact hC
      · exact hmem_tail E hE
    ·

      cases cs_tail with
      | nil => simp at hlen_tail
      | cons D' rest =>
        simp at hhead_tail
        rw [hhead_tail] at hchain_tail ⊢
        exact List.IsChain.cons_cons hAdj_CD hchain_tail

/-- Construct `PrescribedGalleryHypotheses` for a building from the assumption that every apartment chamber has an adjacent chamber. -/
theorem mk_prescribed_gallery_hyp (b : Building V)
    (h_apt_has_adj : ∀ A ∈ b.apartmentSystem.apartments,
      ∀ C, A.IsMaximal C → ∃ D, A.Adjacent C D) :
    PrescribedGalleryHypotheses b where
  apt_gallery_of_type := by
    intro A hA C hC hCmax τ
    exact apt_chain_of_length A (h_apt_has_adj A hA) C hC hCmax τ.length
  apt_adj_implies_bldg_adj := by
    intro A hA C D hC hD hadj
    exact apt_adj_lifts_to_bldg b A hA C D hC hD hadj

end CombinatorialGeometry
