/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Uniqueness
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.ThicknessAptStructureProof
import Atlas.Buildings.code.Building.UniqueRetraction

open scoped Classical

variable {V : Type} [DecidableEq V]

namespace AptFoldingFromRetraction

/-- Thinness of apartments: for every facet $F$ of a maximal chamber $C$ in an apartment $A$,
there is a unique other maximal chamber $D \ne C$ of $A$ with $F$ as a facet. -/
theorem apt_is_thin (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∀ F C, A.IsFacet F C → A.IsMaximal C →
      ∃! D, D ≠ C ∧ A.IsFacet F D ∧ A.IsMaximal D := by

  obtain ⟨B_idx, M, cc, hcc_eq, φ, hinj, hsurj, hadj, hthin⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA

  intro F C hFC hC
  have hFC' : cc.toSimplicialComplex.IsFacet F C := hcc_eq ▸ hFC
  have hC' : cc.toSimplicialComplex.IsMaximal C := hcc_eq ▸ hC
  obtain ⟨D, ⟨hDne, hFD, hDmax⟩, huniq⟩ := hthin F C hFC' hC'
  refine ⟨D, ⟨hDne, hcc_eq ▸ hFD, hcc_eq ▸ hDmax⟩, ?_⟩
  intro D' ⟨hD'ne, hFD', hD'max⟩
  apply huniq
  exact ⟨hD'ne, hcc_eq ▸ hFD', hcc_eq ▸ hD'max⟩

/-- Adjacent chambers have the same cardinality. -/
lemma card_eq_of_adjacent {K : SimplicialComplex V} {C D : Finset V}
    (hadj : K.Adjacent C D) : C.card = D.card := by
  obtain ⟨_, _, _, F, hFC, hFD⟩ := hadj
  have hFC_sub : F ⊆ C := hFC.1.2.2
  have hFD_sub : F ⊆ D := hFD.1.2.2
  have hC_diff : (C \ F).card = 1 := hFC.2
  have hD_diff : (D \ F).card = 1 := hFD.2
  have h1 := Finset.card_sdiff_add_card_inter C F
  have h2 := Finset.card_sdiff_add_card_inter D F
  rw [Finset.inter_eq_right.mpr hFC_sub] at h1
  rw [Finset.inter_eq_right.mpr hFD_sub] at h2
  omega

/-- If a function $f$ is constant along every step of a chain under $R$, then $f$ agrees at the head and last of the chain. -/
lemma list_chain_preserves {α : Type*} {R : α → α → Prop}
    {f : α → ℕ} (hR : ∀ a b, R a b → f a = f b)
    : ∀ (l : List α) (hl : l ≠ []) (_ : List.IsChain R l),
    f (l.head hl) = f (l.getLast hl) := by
  intro l
  induction l with
  | nil => intro hl; exact absurd rfl hl
  | cons hd tl ih =>
    intro _hl hchain
    match tl, ih with
    | [], _ => rfl
    | hd' :: tl', ih =>
      simp only [List.head_cons]
      rw [List.getLast_cons (show (hd' :: tl') ≠ [] from List.cons_ne_nil _ _)]
      rw [List.isChain_cons] at hchain
      have hadj : R hd hd' := by apply hchain.1; simp [List.head?]
      calc f hd = f hd' := hR hd hd' hadj
        _ = f ((hd' :: tl').getLast (List.cons_ne_nil _ _)) :=
            ih (List.cons_ne_nil _ _) hchain.2

/-- Chambers connected by a gallery have the same cardinality. -/
lemma card_eq_of_gallery {K : SimplicialComplex V}
    {C D : Finset V} (g : Gallery K) (hconn : g.Connects C D) :
    C.card = D.card := by
  have hne : g.chambers ≠ [] := by
    intro h
    have : g.chambers.head? = some C := hconn.1
    rw [h] at this
    exact absurd this (by simp)
  have hpres := list_chain_preserves
    (fun a b h => card_eq_of_adjacent h)
    g.chambers hne g.adjacent_consecutive
  have hC : C = g.chambers.head hne := by
    have := hconn.1; rw [List.head?_eq_some_head hne] at this; exact (Option.some_injective _ this).symm
  have hD : D = g.chambers.getLast hne := by
    have := hconn.2; rw [List.getLast?_eq_some_getLast hne] at this; exact (Option.some_injective _ this).symm
  rw [hC, hD]; exact hpres

/-- If $F_0$ is a facet of a chamber $C$ in an apartment $A$ and $F_0 \subseteq D$ for another
maximal chamber $D$ of $A$, then $F_0$ is also a facet of $D$. -/
theorem apt_facet_of_maximal_containing (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    {C D F₀ : Finset V}
    (hC_max : A.IsMaximal C) (hD_max : A.IsMaximal D)
    (hF₀_C : A.IsFacet F₀ C) (hF₀_sub_D : F₀ ⊆ D) :
    A.IsFacet F₀ D := by

  obtain ⟨B_idx, M, cc, hcc_eq, φ, hinj, hsurj, hadj, _⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA

  subst hcc_eq
  obtain ⟨g, hg⟩ := cc.gallery_connected C D hC_max hD_max

  have hcard_eq : C.card = D.card := card_eq_of_gallery g hg

  have hF₀_face : F₀ ∈ cc.toSimplicialComplex.faces := hF₀_C.1.1
  have hF₀_sub_C : F₀ ⊆ C := hF₀_C.1.2.2
  have hC_diff : (C \ F₀).card = 1 := hF₀_C.2

  have hD_diff : (D \ F₀).card = 1 := by
    have h1 := Finset.card_sdiff_add_card_inter C F₀
    have h2 := Finset.card_sdiff_add_card_inter D F₀
    rw [Finset.inter_eq_right.mpr hF₀_sub_C] at h1
    rw [Finset.inter_eq_right.mpr hF₀_sub_D] at h2
    omega

  exact ⟨⟨hF₀_face, hD_max.1, hF₀_sub_D⟩, hD_diff⟩

/-- A retraction fixing vertices of $A$ acts as the identity on faces of $A$. -/
lemma retraction_fixes_face
    {A : SimplicialComplex V}
    {ρ : V → V}
    (hρ_fix : ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v)
    {s : Finset V} (hs : s ∈ A.faces) :
    s.image ρ = s := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [hρ_fix w ⟨s, hs, hw⟩]
  · intro hv
    exact ⟨v, hv, hρ_fix v ⟨s, hs, hv⟩⟩

/-- Thickness yields a third chamber: given adjacent chambers $C, C'$ sharing facet $F$, there
exists $E \notin \{C, C'\}$ also sharing the facet $F$. -/
lemma third_chamber_from_thickness
    {K : ChamberComplex V} (hthick : K.IsThick)
    {C C' : Finset V} (hadj : K.toSimplicialComplex.Adjacent C C') :
    ∃ E F, E ≠ C ∧ E ≠ C' ∧
      K.toSimplicialComplex.IsMaximal E ∧
      K.toSimplicialComplex.IsFacet F C ∧
      K.toSimplicialComplex.IsFacet F C' ∧
      K.toSimplicialComplex.IsFacet F E := by
  obtain ⟨hC_max, _, _, F, hF_C, hF_C'⟩ := hadj
  obtain ⟨D₁, D₂, hD₁_ne_C, hD₂_ne_C, hD₁₂_ne, hFD₁, hD₁_max, hFD₂, hD₂_max⟩ :=
    hthick F C hF_C hC_max
  by_cases h₁ : D₁ = C'
  · exact ⟨D₂, F, hD₂_ne_C, fun h => hD₁₂_ne (h₁ ▸ h.symm), hD₂_max,
          hF_C, hF_C', hFD₂⟩
  · exact ⟨D₁, F, hD₁_ne_C, h₁, hD₁_max, hF_C, hF_C', hFD₁⟩

/-- Uniqueness in thinness: two chambers both opposite to $C$ across the facet $F$ in an apartment must coincide. -/
lemma thin_unique_other_chamber
    {b : Building V}
    {A : SimplicialComplex V} (hA : A ∈ b.apartmentSystem.apartments)
    {F C D₁ D₂ : Finset V}
    (hC_max : A.IsMaximal C)
    (hF_C : A.IsFacet F C)
    (hD₁_max : A.IsMaximal D₁) (hD₁_ne : D₁ ≠ C) (hF_D₁ : A.IsFacet F D₁)
    (hD₂_max : A.IsMaximal D₂) (hD₂_ne : D₂ ≠ C) (hF_D₂ : A.IsFacet F D₂) :
    D₁ = D₂ :=
  ExistsUnique.unique (apt_is_thin b A hA F C hF_C hC_max)
    ⟨hD₁_ne, hF_D₁, hD₁_max⟩ ⟨hD₂_ne, hF_D₂, hD₂_max⟩

/-- In a thin apartment, a maximal chamber containing a facet $F_0$ of two given chambers $C, C'$
must be one of $C$ or $C'$. -/
lemma apt_chamber_with_facet_is_C_or_C'
    {b : Building V}
    {A : SimplicialComplex V} (hA : A ∈ b.apartmentSystem.apartments)
    {C C' D F₀ : Finset V}
    (hC_max : A.IsMaximal C) (hC'_max : A.IsMaximal C')
    (hD_max : A.IsMaximal D)
    (hne : C ≠ C')
    (hF₀_C : A.IsFacet F₀ C) (hF₀_C' : A.IsFacet F₀ C')
    (hF₀_sub_D : F₀ ⊆ D) :
    D = C ∨ D = C' := by
  by_cases hD_eq_C : D = C
  · left; exact hD_eq_C
  · right
    have hF₀_D := apt_facet_of_maximal_containing b A hA hC_max hD_max hF₀_C hF₀_sub_D
    exact (thin_unique_other_chamber hA hC_max hF₀_C hC'_max hne.symm hF₀_C'
      hD_max hD_eq_C hF₀_D).symm

end AptFoldingFromRetraction
