/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.AptThinness

open scoped Classical
open ChamberComplex AptIsCoxeterProof

variable {V : Type} [DecidableEq V]

/-- Boundary-crossing principle: in a chain whose head satisfies $P$ but
some entry does not, there exists an $R$-related adjacent pair witnessing
the transition from $P$ to $\neg P$. -/
theorem chain_transition {α : Type*} (R : α → α → Prop) (P : α → Prop)
    (l : List α) (hchain : List.IsChain R l)
    (hl : l ≠ [])
    (hhead : P (l.head hl))
    (hE : ∃ e ∈ l, ¬P e) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ R a b ∧ P a ∧ ¬P b := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    cases xs with
    | nil =>
      obtain ⟨e, he_mem, he_not⟩ := hE
      simp at he_mem
      subst he_mem
      exact absurd hhead he_not
    | cons y ys =>
      simp only [List.head_cons] at hhead
      by_cases hy : P y
      · have hchain' : List.IsChain R (y :: ys) := List.IsChain.tail hchain
        have hne' : (y :: ys) ≠ [] := List.cons_ne_nil _ _
        obtain ⟨e, he_mem, he_not⟩ := hE
        simp at he_mem
        rcases he_mem with rfl | rfl | he_ys
        · exact absurd hhead he_not
        · exact absurd hy he_not
        · have hE' : ∃ e ∈ (y :: ys), ¬P e := ⟨e, List.mem_cons_of_mem _ he_ys, he_not⟩
          obtain ⟨a, b, ha, hb, hab, hPa, hPb⟩ := ih hchain' hne' hy hE'
          exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hab, hPa, hPb⟩
      · have hRxy : R x y := List.IsChain.rel_head hchain
        exact ⟨x, y, List.mem_cons_self, by simp, hRxy, hhead, hy⟩

namespace ThicknessFoldings

/-- Every apartment is thin: each facet $F \subset C$ lies in exactly one
other chamber $D$ of the apartment. -/
theorem apt_is_thin_pre (K : ChamberComplex V)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∀ F C, A.IsFacet F C → A.IsMaximal C →
      ∃! D, D ≠ C ∧ A.IsFacet F D ∧ A.IsMaximal D := by
  obtain ⟨cc, hcc_eq, hcc_thin⟩ := pre.apt_thin_cc A hA
  intro F C hFC hC
  have hFC' : cc.toSimplicialComplex.IsFacet F C := hcc_eq ▸ hFC
  have hC' : cc.toSimplicialComplex.IsMaximal C := hcc_eq ▸ hC
  obtain ⟨D, ⟨hDne, hFD, hDmax⟩, huniq⟩ := hcc_thin F C hFC' hC'
  refine ⟨D, ⟨hDne, hcc_eq ▸ hFD, hcc_eq ▸ hDmax⟩, ?_⟩
  intro D' ⟨hD'ne, hFD', hD'max⟩
  apply huniq
  exact ⟨hD'ne, hcc_eq ▸ hFD', hcc_eq ▸ hD'max⟩

/-- Chamber transitivity for the pre-apartment system: for any two chambers
$C, D$ of an apartment, there is a bijective vertex map sending $C$ to $D$. -/
theorem apt_automorphism_sending_chamber_pre
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (D : Finset V) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C :=
  pre.apt_automorphism A hA C hC D hD


/-- Any apartment iso fixing a chamber is bijective (pre-apartment version). -/
theorem iso_bijective_fixing_chamber_pre
    (pre : PreApartmentData K)
    (B : SimplicialComplex V) (hB : B ∈ pre.apartments)
    (B₀ : SimplicialComplex V) (hB₀ : B₀ ∈ pre.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces) (hD_B₀ : D ∈ B₀.faces)
    (hD_max_B : B.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧
      D.image φ = D := by
  obtain ⟨ψ, hψ_bij, hψ_faces⟩ :=
    pre.iso_bijective B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
  have hDψ_max_B₀ : B₀.IsMaximal (D.image ψ) :=
    bijective_face_iso_preserves_maximal hψ_bij hψ_faces hD_max_B
  have hD_max_B₀ : B₀.IsMaximal D :=
    pre.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀
      (pre.maximal_in_apt_is_maximal B hB D hD_max_B)
  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber_pre pre B₀ hB₀ D hD_max_B₀ (D.image ψ) hDψ_max_B₀
  refine ⟨α ∘ ψ, hα_bij.comp hψ_bij, ?_, ?_⟩
  · intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hψ_faces s) (hα_faces (s.image ψ))
  · simp only [← Finset.image_image]
    exact hα_send


/-- A facet $F$ contained in a maximal chamber $C$ of an apartment is a
facet of $C$ in the apartment. -/
theorem apt_facet_of_maximal_containing_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    {C D F₀ : Finset V}
    (hC_max : A.IsMaximal C) (hD_max : A.IsMaximal D)
    (hF₀_C : A.IsFacet F₀ C) (hF₀_sub_D : F₀ ⊆ D) :
    A.IsFacet F₀ D := by
  obtain ⟨cc, hcc_eq, _hcc_thin⟩ := pre.apt_thin_cc A hA
  subst hcc_eq
  obtain ⟨g, hg⟩ := cc.gallery_connected C D hC_max hD_max
  have hcard_eq : C.card = D.card :=
    AptFoldingFromRetraction.card_eq_of_gallery g hg
  have hF₀_sub_C : F₀ ⊆ C := hF₀_C.1.2.2
  have hC_diff : (C \ F₀).card = 1 := hF₀_C.2
  have hD_diff : (D \ F₀).card = 1 := by
    have h1 := Finset.card_sdiff_add_card_inter C F₀
    have h2 := Finset.card_sdiff_add_card_inter D F₀
    rw [Finset.inter_eq_right.mpr hF₀_sub_C] at h1
    rw [Finset.inter_eq_right.mpr hF₀_sub_D] at h2
    omega
  exact ⟨⟨hF₀_C.1.1, hD_max.1, hF₀_sub_D⟩, hD_diff⟩

/-- Pre-apartment thinness: each facet $F$ has a unique other chamber $D$
besides $C$ in the apartment. -/
lemma thin_unique_other_chamber_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
    {F C D₁ D₂ : Finset V}
    (hC_max : A.IsMaximal C)
    (hF_C : A.IsFacet F C)
    (hD₁_max : A.IsMaximal D₁) (hD₁_ne : D₁ ≠ C) (hF_D₁ : A.IsFacet F D₁)
    (hD₂_max : A.IsMaximal D₂) (hD₂_ne : D₂ ≠ C) (hF_D₂ : A.IsFacet F D₂) :
    D₁ = D₂ :=
  ExistsUnique.unique (apt_is_thin_pre K pre A hA F C hF_C hC_max)
    ⟨hD₁_ne, hF_D₁, hD₁_max⟩ ⟨hD₂_ne, hF_D₂, hD₂_max⟩

/-- A chamber of the apartment containing a facet $F$ is either $C$ or its
unique opposite chamber across $F$. -/
lemma apt_chamber_with_facet_is_C_or_C_pre
    (K : ChamberComplex V)
    (pre : PreApartmentData K)
    {A : SimplicialComplex V} (hA : A ∈ pre.apartments)
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
    have hF₀_D := apt_facet_of_maximal_containing_pre K pre A hA hC_max hD_max hF₀_C hF₀_sub_D
    exact (thin_unique_other_chamber_pre K pre hA hC_max hF₀_C hC'_max hne.symm hF₀_C'
      hD_max hD_eq_C hF₀_D).symm


/-- Construct a folding from a simplicial map fixing a chamber and sending
its panel-mate to itself — the third-chamber map of a thick complex. -/
theorem folding_from_simplicial_map
    (cc : ChamberComplex V) (hthin : cc.IsThin)
    (f : V → V)
    (hface : ∀ s ∈ cc.toSimplicialComplex.faces,
      s.image f ∈ cc.toSimplicialComplex.faces)
    (hidempotent : ∀ v, f (f v) = f v)
    (hchamberMap : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      cc.toSimplicialComplex.IsMaximal (D.image f))
    (hpreservesFacets : ∀ F D, cc.toSimplicialComplex.IsFacet F D →
      cc.toSimplicialComplex.IsFacet (F.image f) (D.image f))
    (htwoToOne : ∀ D, cc.toSimplicialComplex.IsMaximal D →
      D.image f = D →
      ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D)
    (hstutter_contradicts_minimality :
      ∀ (A B : Finset V),
        cc.toSimplicialComplex.IsMaximal A → A.image f = A →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A B →
        g.length = galleryDist cc.toSimplicialComplex A B →
        ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
          cc.toSimplicialComplex.Adjacent Ci Ci1 →
          Ci1.image f = Ci.image f → False)
    (C C' : Finset V)
    (hadj : cc.toSimplicialComplex.Adjacent C C')
    (hfC : C.image f = C)
    (hfC' : C'.image f = C) :
    ∃ fold : Folding cc,
      C.image fold.morph.toFun = C ∧ C'.image fold.morph.toFun = C := by

  have hCmax : cc.toSimplicialComplex.IsMaximal C := hadj.1
  have hC'max : cc.toSimplicialComplex.IsMaximal C' := hadj.2.1
  have hne : C ≠ C' := hadj.2.2.1
  obtain ⟨F, hFC, hFC'⟩ := hadj.2.2.2

  let morph : SimplicialComplex.Morphism cc.toSimplicialComplex cc.toSimplicialComplex :=
    ⟨f, hface⟩

  have fixes_pointwise_of_fixed : ∀ (D : Finset V), D.image f = D → ∀ v ∈ D, f v = v := by
    intro D hD v hv
    rw [← hD] at hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    rw [← huv, hidempotent]

  have hC'moved : C'.image f ≠ C' := by
    rw [hfC']; exact fun h => hne (h ▸ rfl)

  have hnot_id : ∃ D, cc.toSimplicialComplex.IsMaximal D ∧ D.image f ≠ D := by
    exact ⟨C', hC'max, hC'moved⟩

  have hstutter_at_boundary :
      ∀ (Ci Ci1 : Finset V),
        cc.toSimplicialComplex.Adjacent Ci Ci1 →
        (cc.toSimplicialComplex.IsMaximal Ci ∧ Ci.image f = Ci) →
        Ci1.image f ≠ Ci1 →
        Ci1.image f = Ci := by
    intro Ci Ci1 hadj_pair ⟨hCimax, hfCi⟩ hCi1moved
    obtain ⟨_, hCi1max, hne_pair, G, hGCi, hGCi1⟩ := hadj_pair

    have hfix := fixes_pointwise_of_fixed Ci hfCi
    have hfG : G.image f = G := by
      ext v; simp only [Finset.mem_image]; constructor
      · rintro ⟨w, hw, rfl⟩; rwa [hfix w (hGCi.1.2.2 hw)]
      · intro hv; exact ⟨v, hv, hfix v (hGCi.1.2.2 hv)⟩

    have hfGfCi1 := hpreservesFacets G Ci1 hGCi1
    rw [hfG] at hfGfCi1

    have hfCi1max := hchamberMap Ci1 hCi1max

    obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hthin G Ci hGCi hCimax


    by_contra hfCi1_ne_Ci
    have hCi1_eq_D' : Ci1 = D' := hD'uniq Ci1 ⟨hne_pair.symm, hGCi1, hCi1max⟩
    have : Ci1.image f = D' :=
      hD'uniq (Ci1.image f) ⟨hfCi1_ne_Ci, hfGfCi1, hfCi1max⟩
    rw [← hCi1_eq_D'] at this
    exact hCi1moved this

  have hexists_boundary : ∃ A B, cc.toSimplicialComplex.Adjacent A B ∧
      A.image f = A ∧ B.image f ≠ B := by
    exact ⟨C, C', hadj, hfC, hC'moved⟩


  have hgallery_exits :
      ∀ (A B : Finset V),
        cc.toSimplicialComplex.IsMaximal A → A.image f = A →
        cc.toSimplicialComplex.IsMaximal B → B.image f = B →
        ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A B →
        ∀ (E : Finset V), E ∈ g.chambers → E.image f ≠ E →
        ∃ Ci Ci1, Ci ∈ g.chambers ∧ Ci1 ∈ g.chambers ∧
          cc.toSimplicialComplex.Adjacent Ci Ci1 ∧
          (cc.toSimplicialComplex.IsMaximal Ci ∧ Ci.image f = Ci) ∧
          ¬(cc.toSimplicialComplex.IsMaximal Ci1 ∧ Ci1.image f = Ci1) := by
    intro A' B' hA'max hfA' hB'max hfB' g hconn E hE_mem hE_moved

    let P := fun (D : Finset V) => cc.toSimplicialComplex.IsMaximal D ∧ D.image f = D
    have hl_ne : g.chambers ≠ [] := by
      intro h; have := g.length_pos; rw [h] at this; simp at this
    have hhead_P : P (g.chambers.head hl_ne) := by
      have := hconn.1
      rw [List.head?_eq_some_head hl_ne] at this
      simp at this; rw [this]; exact ⟨hA'max, hfA'⟩
    have hE_notP : ∃ e ∈ g.chambers, ¬P e := by
      refine ⟨E, hE_mem, ?_⟩
      intro ⟨_, hfE⟩; exact hE_moved hfE
    obtain ⟨a, b, ha, hb, hadj_ab, hPa, hPb⟩ :=
      chain_transition cc.toSimplicialComplex.Adjacent P g.chambers
        g.adjacent_consecutive hl_ne hhead_P hE_notP
    exact ⟨a, b, ha, hb, hadj_ab, hPa, hPb⟩

  exact ⟨⟨morph, hchamberMap, hpreservesFacets, hidempotent, hnot_id,
    htwoToOne, hexists_boundary, hgallery_exits, hstutter_at_boundary,
    hstutter_contradicts_minimality⟩, hfC, hfC'⟩



end ThicknessFoldings
