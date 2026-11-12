/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
import Atlas.Buildings.code.Building.StrongIsometryExtMain

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- Configuration of three chambers $C, D, E$ in a building, with apartments through each pair. -/
structure ThreeChamberConfig (b : Building V) where
  C : Finset V
  D : Finset V
  E : Finset V
  hC : b.toSimplicialComplex.IsMaximal C
  hD : b.toSimplicialComplex.IsMaximal D
  hE : b.toSimplicialComplex.IsMaximal E
  apt_CD : SimplicialComplex V
  apt_CD_mem : apt_CD ∈ b.apartmentSystem.apartments
  hC_CD : C ∈ apt_CD.faces
  hD_CD : D ∈ apt_CD.faces
  apt_CE : SimplicialComplex V
  apt_CE_mem : apt_CE ∈ b.apartmentSystem.apartments
  hC_CE : C ∈ apt_CE.faces
  hE_CE : E ∈ apt_CE.faces
  apt_DE : SimplicialComplex V
  apt_DE_mem : apt_DE ∈ b.apartmentSystem.apartments
  hD_DE : D ∈ apt_DE.faces
  hE_DE : E ∈ apt_DE.faces

/-- Triangle inequality for gallery distance: $d(C, E) \le d(C, D) + d(D, E)$. -/
def ThreeChamberConfig.TriangleInequality {b : Building V}
    (cfg : ThreeChamberConfig b) : Prop :=
  galleryDist b.toSimplicialComplex cfg.C cfg.E ≤
    galleryDist b.toSimplicialComplex cfg.C cfg.D +
    galleryDist b.toSimplicialComplex cfg.D cfg.E

/-- Three chambers $C, D, E$ are *collinear* if $d(C, E) = d(C, D) + d(D, E)$ (i.e. $D$ lies on a
minimal gallery from $C$ to $E$). -/
def ThreeChamberConfig.IsCollinear {b : Building V}
    (cfg : ThreeChamberConfig b) : Prop :=
  galleryDist b.toSimplicialComplex cfg.C cfg.E =
    galleryDist b.toSimplicialComplex cfg.C cfg.D +
    galleryDist b.toSimplicialComplex cfg.D cfg.E

/-- A *strong isometry* between subsets of chambers $S_1, S_2$ is a map preserving the Weyl-valued
distance $\delta_W$. -/
def StrongIsometry {b : Building V} (δW : Building.WValuedDist b)
    (S₁ S₂ : Set (Finset V))
    (φ : Finset V → Finset V) : Prop :=
  IsStrongIsometry δW S₁ S₂ φ

/-- $S$ *lies in an apartment* if there is some apartment $A$ of the building whose face set contains $S$. -/
def SubsetInApartment (b : Building V)
    (S : Set (Finset V)) : Prop :=
  ∃ A ∈ b.apartmentSystem.apartments, ∀ C ∈ S, C ∈ A.faces


/-- The identity map is a strong $\delta_W$-isometry from $S$ to itself. -/
lemma identity_strong_isometry_of_subset {b : Building V}
    (δW : Building.WValuedDist b)
    (S : Set (Finset V))
    (A : SimplicialComplex V) (_hA : A ∈ b.apartmentSystem.apartments)
    (hS : ∀ C ∈ S, C ∈ A.faces)
    (_hS_max : ∀ C ∈ S, b.toSimplicialComplex.IsMaximal C) :
    IsStrongIsometry δW S S id ∧ (∀ C ∈ S, id C ∈ A.faces) := by
  refine ⟨⟨fun C hC => hC, fun C hC => ⟨C, hC, rfl⟩, fun C hC D hD => rfl⟩,
          fun C hC => hS C hC⟩

/-- Hypotheses underlying the three-chamber argument: concatenability of galleries and existence of
a minimal gallery between any two maximal chambers. -/
structure ThreeChamberHypotheses (b : Building V) where
  gallery_concat :
    ∀ (C₁ C₂ C₃ : Finset V)
      (g₁ g₂ : Gallery b.toSimplicialComplex),
      g₁.Connects C₁ C₂ → g₂.Connects C₂ C₃ →
      ∃ g₃ : Gallery b.toSimplicialComplex,
        g₃.Connects C₁ C₃ ∧
        g₃.length = g₁.length + g₂.length ∧
        C₂ ∈ g₃.chambers
  minimal_gallery_exists :
    ∀ (C D : Finset V),
      b.toSimplicialComplex.IsMaximal C →
      b.toSimplicialComplex.IsMaximal D →
      ∃ g : Gallery b.toSimplicialComplex,
        g.Connects C D ∧ g.length = galleryDist b.toSimplicialComplex C D

/-- Every building canonically satisfies `ThreeChamberHypotheses`. -/
theorem threeChamberHypotheses_of_building (b : Building V) :
    ThreeChamberHypotheses b where
  gallery_concat := by
    intro C₁ C₂ C₃ g₁ g₂ hconn₁ hconn₂
    have hne₁ : g₁.chambers ≠ [] := List.ne_nil_of_length_pos g₁.length_pos
    have hne₂ : g₂.chambers ≠ [] := List.ne_nil_of_length_pos g₂.length_pos

    have hhead₂ : g₂.chambers.head? = some C₂ := hconn₂.1
    have hlast₁ : g₁.chambers.getLast? = some C₂ := hconn₁.2
    have hlast₂ : g₂.chambers.getLast? = some C₃ := hconn₂.2

    have ⟨rest₂, hg₂_eq⟩ : ∃ rest₂, g₂.chambers = C₂ :: rest₂ := by
      obtain ⟨a, t, heq⟩ := List.exists_cons_of_ne_nil hne₂
      rw [heq, List.head?] at hhead₂
      simp at hhead₂
      exact ⟨t, by rw [heq, hhead₂]⟩

    set cs := g₁.chambers ++ rest₂ with cs_def
    have hcs_pos : cs.length > 0 := by
      rw [cs_def, List.length_append]
      have := g₁.length_pos
      omega
    have hcs_max : ∀ C ∈ cs, b.toSimplicialComplex.IsMaximal C := by
      intro C hC
      rw [cs_def, List.mem_append] at hC
      rcases hC with h | h
      · exact g₁.all_maximal C h
      · exact g₂.all_maximal C (hg₂_eq ▸ List.mem_cons_of_mem _ h)

    have hcs_chain : List.IsChain b.toSimplicialComplex.Adjacent cs := by
      rw [cs_def, List.isChain_append]
      refine ⟨g₁.adjacent_consecutive, (hg₂_eq ▸ g₂.adjacent_consecutive).tail, ?_⟩
      intro x hx y hy
      rw [Option.mem_def] at hx hy

      have hx_eq : x = C₂ := by
        have : g₁.chambers.getLast? = some x := hx
        rw [hlast₁] at this
        exact (Option.some_injective _ this).symm
      subst hx_eq

      cases rest₂ with
      | nil => simp [List.head?] at hy
      | cons a t =>
        simp [List.head?] at hy
        subst hy
        exact (hg₂_eq ▸ g₂.adjacent_consecutive).rel_head

    refine ⟨⟨cs, hcs_pos, hcs_max, hcs_chain⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    ·
      show cs.head? = some C₁
      rw [cs_def, List.head?_append_of_ne_nil _ hne₁]
      exact hconn₁.1
    ·
      show cs.getLast? = some C₃
      rw [cs_def, List.getLast?_append]
      cases rest₂ with
      | nil =>
        simp [Option.or, List.getLast?]

        rw [hg₂_eq] at hlast₂
        simp [List.getLast?] at hlast₂
        rw [← hlast₂]
        exact hlast₁
      | cons a t =>
        have hne_rest : (a :: t) ≠ [] := List.cons_ne_nil _ _
        have hsome := List.getLast?_eq_some_getLast hne_rest
        rw [hsome, Option.some_or]
        rw [hg₂_eq] at hlast₂
        rw [List.getLast?_cons_cons] at hlast₂
        rw [← hsome]
        exact hlast₂
    ·
      show cs.length - 1 = g₁.length + g₂.length
      rw [cs_def, List.length_append]
      simp only [Gallery.length]
      have hg₂_len : g₂.chambers.length = rest₂.length + 1 := by
        rw [hg₂_eq, List.length_cons]
      have := g₁.length_pos
      omega
    ·
      show C₂ ∈ cs
      rw [cs_def, List.mem_append]
      left
      exact List.mem_of_getLast? hlast₁
  minimal_gallery_exists := by
    intro C D hC hD
    by_cases h : C = D
    ·
      subst h
      exact ⟨⟨[C], by simp, fun E hE => by simp at hE; subst hE; exact hC,
              List.IsChain.singleton C⟩,
             ⟨by simp, by simp⟩,
             by simp [Gallery.length, galleryDist_self]⟩
    ·
      obtain ⟨g₀, hconn₀⟩ := b.toChamberComplex.gallery_connected C D hC hD
      have hne : {n | ∃ g : Gallery b.toSimplicialComplex, g.Connects C D ∧ g.length = n}.Nonempty :=
        ⟨g₀.length, g₀, ⟨hconn₀.1, hconn₀.2⟩, rfl⟩
      obtain ⟨g, hconn, hlen⟩ := Nat.sInf_mem hne
      exact ⟨g, hconn, by unfold galleryDist; rw [if_neg h]; exact hlen⟩

/-- Three-chambers-in-a-common-apartment: if $C_1, C_2, C_3$ are collinear chambers (i.e.
$d(C_1, C_3) = d(C_1, C_2) + d(C_2, C_3)$), then they all lie in some common apartment. -/
theorem three_chambers_common_apartment (b : Building V)
    (hyp : ThreeChamberHypotheses b)
    (C₁ C₂ C₃ : Finset V)
    (hC₁ : b.toSimplicialComplex.IsMaximal C₁)
    (hC₂ : b.toSimplicialComplex.IsMaximal C₂)
    (hC₃ : b.toSimplicialComplex.IsMaximal C₃)
    (hcollinear : galleryDist b.toSimplicialComplex C₁ C₃ =
      galleryDist b.toSimplicialComplex C₁ C₂ +
      galleryDist b.toSimplicialComplex C₂ C₃) :
    ∃ A ∈ b.apartmentSystem.apartments,
      C₁ ∈ A.faces ∧ C₂ ∈ A.faces ∧ C₃ ∈ A.faces := by

  obtain ⟨g₁, hconn₁, hmin₁⟩ := hyp.minimal_gallery_exists C₁ C₂ hC₁ hC₂
  obtain ⟨g₂, hconn₂, hmin₂⟩ := hyp.minimal_gallery_exists C₂ C₃ hC₂ hC₃

  obtain ⟨g₃, hconn₃, hlen₃, hC₂_mem⟩ :=
    hyp.gallery_concat C₁ C₂ C₃ g₁ g₂ hconn₁ hconn₂

  have hmin₃ : g₃.length = galleryDist b.toSimplicialComplex C₁ C₃ := by
    rw [hlen₃, hmin₁, hmin₂, ← hcollinear]

  obtain ⟨A, hA, hC₁A, hC₃A⟩ := b.apartmentSystem.contains_pair C₁ C₃ hC₁ hC₃

  have hall_in_A : ∀ E ∈ g₃.chambers, E ∈ A.faces :=
    b.apartmentSystem.gallery_convex A hA C₁ C₃ hC₁A hC₁ hC₃A hC₃ g₃ hconn₃ hmin₃

  exact ⟨A, hA, hC₁A, hall_in_A C₂ hC₂_mem, hC₃A⟩

end CombinatorialGeometry
