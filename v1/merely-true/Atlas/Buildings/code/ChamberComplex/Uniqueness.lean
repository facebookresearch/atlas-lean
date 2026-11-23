/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Basic

open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

namespace SimplicialComplex

/-- A simplicial morphism $K \to L$: a vertex map sending each face of $K$ to a face of $L$. -/
structure Morphism (K : SimplicialComplex V) (L : SimplicialComplex W) where
  toFun : V → W
  map_face : ∀ s ∈ K.faces, s.image toFun ∈ L.faces

/-- A morphism is a *chamber map* if it sends maximal faces to maximal faces. -/
def Morphism.IsChamberMap {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ C, K.IsMaximal C → L.IsMaximal (C.image f.toFun)

/-- A morphism *preserves facets* if codim-$1$ inclusions in $K$ go to codim-$1$ inclusions in $L$. -/
def Morphism.PreservesFacets {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ F C, K.IsFacet F C → L.IsFacet (F.image f.toFun) (C.image f.toFun)

/-- Two morphisms `f, g` *agree on $C$* if they coincide on every vertex of $C$. -/
def AgreeOn {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) (C : Finset V) : Prop :=
  ∀ v ∈ C, f.toFun v = g.toFun v

/-- Two morphisms have *equal image on $C$*: $f(C) = g(C)$ as sets. -/
def AgreeOnImage {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) (C : Finset V) : Prop :=
  C.image f.toFun = C.image g.toFun

/-- The "at most two chambers per facet" property: a facet $F$ lies in at most two chambers. -/
def AtMostTwoChambers (L : SimplicialComplex W) : Prop :=
  ∀ F C D E, L.IsFacet F C → L.IsMaximal C →
    L.IsFacet F D → L.IsMaximal D → D ≠ C →
    L.IsFacet F E → L.IsMaximal E → E ≠ C →
    D = E

/-- A morphism is *non-stuttering on adjacent pairs*: it never collapses adjacent chambers. -/
def Morphism.NonStutteringAdj {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ C D, K.Adjacent C D → C.image f.toFun ≠ D.image f.toFun

/-- *Sub-face compatibility*: if $f, g$ agree on the image of a chamber $C$, then they agree on
the image of any face of $C$. -/
def SubFaceCompatible {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) : Prop :=
  ∀ C, K.IsMaximal C → AgreeOnImage f g C →
    ∀ F, K.IsFace F C → AgreeOnImage f g F

/-- Pointwise agreement on $C$ implies image agreement on $C$. -/
lemma agreeOn_imp_agreeOnImage {K : SimplicialComplex V} {L : SimplicialComplex W}
    {f g : Morphism K L} {C : Finset V} (h : AgreeOn f g C) :
    AgreeOnImage f g C := by
  unfold AgreeOnImage
  apply Finset.image_congr
  intro x hx
  exact h x hx

/-- Inductive step: if $f, g$ agree on the image of $C_1$ and $C_1, C_2$ are adjacent, then under
the hypotheses (at-most-two, chamber maps, facet preservation, non-stutter, sub-face compatible)
they also agree on the image of $C_2$. -/
lemma agree_image_next_chamber
    {K : SimplicialComplex V} {L : SimplicialComplex W}
    (hL : AtMostTwoChambers L)
    (f g : Morphism K L) (hf : f.IsChamberMap) (hg : g.IsChamberMap)
    (hfF : f.PreservesFacets) (hgF : g.PreservesFacets)
    (hf_ns : f.NonStutteringAdj) (hg_ns : g.NonStutteringAdj)
    (hcompat : SubFaceCompatible f g)
    {C₁ C₂ : Finset V}
    (hadj : K.Adjacent C₁ C₂)
    (hC₁_max : K.IsMaximal C₁)
    (hagree : AgreeOnImage f g C₁) :
    AgreeOnImage f g C₂ := by

  have hadj' := hadj
  obtain ⟨_, hC₂, _, F, hFC₁, hFC₂⟩ := hadj'

  have hFimg : AgreeOnImage f g F := hcompat C₁ hC₁_max hagree F hFC₁.1

  have hfFC₂ : L.IsFacet (F.image f.toFun) (C₂.image f.toFun) := hfF F C₂ hFC₂

  have hgFC₂ : L.IsFacet (F.image f.toFun) (C₂.image g.toFun) :=
    hFimg ▸ hgF F C₂ hFC₂

  have hfFC₁ : L.IsFacet (F.image f.toFun) (C₁.image f.toFun) := hfF F C₁ hFC₁

  have hfC₁_max : L.IsMaximal (C₁.image f.toFun) := hf C₁ hC₁_max
  have hfC₂_max : L.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂
  have hgC₂_max : L.IsMaximal (C₂.image g.toFun) := hg C₂ hC₂

  have hf_ne : C₁.image f.toFun ≠ C₂.image f.toFun := hf_ns C₁ C₂ hadj

  have hg_ne : C₁.image f.toFun ≠ C₂.image g.toFun := hagree ▸ hg_ns C₁ C₂ hadj

  exact hL (F.image f.toFun) (C₁.image f.toFun) (C₂.image f.toFun) (C₂.image g.toFun)
    hfFC₁ hfC₁_max hfFC₂ hfC₂_max (Ne.symm hf_ne) hgFC₂ hgC₂_max (Ne.symm hg_ne)

set_option linter.unusedSectionVars false in
/-- If `l.getLast? = some a` then `a ∈ l`. -/
lemma mem_of_getLast?_eq_some {α : Type*} {l : List α} {a : α}
    (h : l.getLast? = some a) : a ∈ l := by
  rw [List.getLast?_eq_some_iff] at h
  obtain ⟨ys, rfl⟩ := h
  simp

/-- Propagate image-agreement of $f, g$ along an entire chain of chambers via successive
applications of `agree_image_next_chamber`. -/
lemma agree_image_along_chain
    {K : SimplicialComplex V} {L : SimplicialComplex W}
    (hL : AtMostTwoChambers L)
    (f g : Morphism K L) (hf : f.IsChamberMap) (hg : g.IsChamberMap)
    (hfF : f.PreservesFacets) (hgF : g.PreservesFacets)
    (hf_ns : f.NonStutteringAdj) (hg_ns : g.NonStutteringAdj)
    (hcompat : SubFaceCompatible f g)
    (cs : List (Finset V))
    (hne : cs ≠ [])
    (hchain : List.IsChain K.Adjacent cs)
    (hall : ∀ C ∈ cs, K.IsMaximal C)
    (hagree : AgreeOnImage f g (cs.head hne)) :
    ∀ D ∈ cs, AgreeOnImage f g D := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro D hD
    rw [List.mem_cons] at hD
    rcases hD with rfl | hD
    · exact hagree
    · cases tl with
      | nil => simp at hD
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : K.Adjacent a b := hrel b rfl
        have ha_max : K.IsMaximal a := hall a (List.mem_cons_self)

        have hagree_b : AgreeOnImage f g b :=
          agree_image_next_chamber hL f g hf hg hfF hgF hf_ns hg_ns hcompat
            hab ha_max hagree

        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun C hC => hall C (List.mem_cons_of_mem a hC))
          hagree_b D hD

/-- *Uniqueness Lemma 3.2*: in a chamber complex $K$ with $L$ satisfying the at-most-two
property, two chamber maps with matching image on some chamber $C$ have matching image on every
chamber of $K$ — i.e. they are determined by their action on a single chamber. -/
theorem uniqueness_lemma_32
    {K : ChamberComplex V} {L : SimplicialComplex W}
    (hL : AtMostTwoChambers L)
    (f g : Morphism K.toSimplicialComplex L)
    (hf : f.IsChamberMap) (hg : g.IsChamberMap)
    (hfF : f.PreservesFacets) (hgF : g.PreservesFacets)
    (hf_ns : f.NonStutteringAdj) (hg_ns : g.NonStutteringAdj)
    (hcompat : SubFaceCompatible f g)
    (C : Finset V) (hC : K.toSimplicialComplex.IsMaximal C)
    (hagree : AgreeOnImage f g C) :
    ∀ D, K.toSimplicialComplex.IsMaximal D → AgreeOnImage f g D := by
  intro D hD

  obtain ⟨gal, hgal_head, hgal_last⟩ := K.gallery_connected C D hC hD

  have hD_mem : D ∈ gal.chambers := mem_of_getLast?_eq_some hgal_last

  have hne : gal.chambers ≠ [] := by
    intro h; simp [h] at hgal_head

  have hhead_eq : gal.chambers.head hne = C := by
    rw [List.head?_eq_some_head hne] at hgal_head
    exact Option.some_injective _ hgal_head

  exact agree_image_along_chain hL f g hf hg hfF hgF hf_ns hg_ns hcompat
    gal.chambers hne gal.adjacent_consecutive gal.all_maximal
    (hhead_eq ▸ hagree) D hD_mem

/-- If $f$ fixes $C$ pointwise then $f(C) = C$ as a set. -/
lemma image_eq_of_fixes_pointwise {f : V → V} {C : Finset V}
    (h : ∀ v ∈ C, f v = v) : C.image f = C := by
  ext x; simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [h y hy]
  · intro hx; exact ⟨x, hx, h x hx⟩

/-- If $F \subseteq C$ with $|C \setminus F| = 1$, $f$ fixes $F$ pointwise, and $f(C) = C$ then
$f$ fixes the whole $C$ pointwise. -/
lemma fixes_pointwise_of_facet_and_image {f : V → V} {C F : Finset V}
    (hFC : F ⊆ C)
    (hcard : (C \ F).card = 1)
    (hfixF : ∀ v ∈ F, f v = v)
    (himg : C.image f = C) :
    ∀ v ∈ C, f v = v := by
  intro v hv
  by_cases hvF : v ∈ F
  · exact hfixF v hvF
  · have hv_diff : v ∈ C \ F := Finset.mem_sdiff.mpr ⟨hv, hvF⟩
    have hsingleton : C \ F = {v} := by
      rw [Finset.card_eq_one] at hcard
      obtain ⟨w, hw⟩ := hcard
      have : v = w := by rw [hw] at hv_diff; simp at hv_diff; exact hv_diff
      rw [this]; exact hw
    have hC_eq : C = F ∪ {v} := by
      ext x; constructor
      · intro hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        by_cases hxF : x ∈ F
        · left; exact hxF
        · right
          have : x ∈ C \ F := Finset.mem_sdiff.mpr ⟨hx, hxF⟩
          rw [hsingleton] at this; simp at this; exact this
      · simp only [Finset.mem_union, Finset.mem_singleton]
        rintro (hx | rfl)
        · exact hFC hx
        · exact hv
    rw [hC_eq, Finset.image_union, Finset.image_singleton] at himg
    have hFimg : F.image f = F := image_eq_of_fixes_pointwise hfixF
    rw [hFimg] at himg
    have hv_mem : v ∈ F ∪ {f v} := by rw [himg]; simp
    simp only [Finset.mem_union, Finset.mem_singleton] at hv_mem
    exact hv_mem.elim (fun h => absurd h hvF) Eq.symm

/-- In a thin complex: if $f$ fixes $C_1$ pointwise and $f(C_2) \neq C_1$ (no "fold back"), then
$f$ fixes the adjacent chamber $C_2$ pointwise too. -/
lemma thin_fixes_next_chamber
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap) (hfF : f.PreservesFacets)
    {C₁ C₂ : Finset V}
    (hadj : X.toSimplicialComplex.Adjacent C₁ C₂)
    (hfix₁ : ∀ v ∈ C₁, f.toFun v = v)
    (hne : C₂.image f.toFun ≠ C₁) :
    ∀ v ∈ C₂, f.toFun v = v := by
  obtain ⟨hC₁max, hC₂max, hC₁C₂, F, hFC₁, hFC₂⟩ := hadj

  have hF_sub_C₁ : F ⊆ C₁ := hFC₁.1.2.2
  have hfixF : ∀ v ∈ F, f.toFun v = v := fun v hv => hfix₁ v (hF_sub_C₁ hv)

  have hFimg : F.image f.toFun = F := image_eq_of_fixes_pointwise hfixF

  have hfacet : X.toSimplicialComplex.IsFacet (F.image f.toFun) (C₂.image f.toFun) :=
    hfF F C₂ hFC₂
  rw [hFimg] at hfacet

  have hfC₂max : X.toSimplicialComplex.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂max

  have hthin_inst := hthin F C₁ hFC₁ hC₁max
  obtain ⟨D, ⟨hDC₁, hFD, hDmax⟩, huniq⟩ := hthin_inst

  have hC₂_eq_D : C₂ = D := huniq C₂ ⟨hC₁C₂.symm, hFC₂, hC₂max⟩

  have hfC₂_eq_D : C₂.image f.toFun = D :=
    huniq (C₂.image f.toFun) ⟨hne, hfacet, hfC₂max⟩

  have hC₂img : C₂.image f.toFun = C₂ := by rw [hfC₂_eq_D, ← hC₂_eq_D]

  exact fixes_pointwise_of_facet_and_image hFC₂.1.2.2 hFC₂.2 hfixF hC₂img

/-- The image gallery $(C \mapsto f(C))$ stutters: some adjacent images are equal. -/
def GalleryStuttersUnder (cs : List (Finset V)) (f : V → V) : Prop :=
  ¬ List.IsChain (· ≠ ·) (cs.map (fun C => C.image f))

/-- $f$ fixes every chamber of $cs$ pointwise. -/
def FixesAllPointwise (cs : List (Finset V)) (f : V → V) : Prop :=
  ∀ C ∈ cs, ∀ v ∈ C, f v = v

/-- Variant of `thin_fixes_next_chamber` extended along an entire non-stuttering chain. -/
lemma fixes_along_chain_of_nonstuttering
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap) (hfF : f.PreservesFacets)
    (cs : List (Finset V))
    (hne : cs ≠ [])
    (hchain : List.IsChain X.toSimplicialComplex.Adjacent cs)
    (hall : ∀ C ∈ cs, X.toSimplicialComplex.IsMaximal C)
    (hfix_head : ∀ v ∈ cs.head hne, f.toFun v = v)
    (hns : List.IsChain (· ≠ ·) (cs.map (fun C => C.image f.toFun))) :
    ∀ C ∈ cs, ∀ v ∈ C, f.toFun v = v := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro C hC
    rw [List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact hfix_head
    · cases tl with
      | nil => simp at hC
      | cons b rest =>

        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : X.toSimplicialComplex.Adjacent a b := hrel b rfl

        have hns_cons : List.IsChain (· ≠ ·)
            ((a.image f.toFun) :: (b :: rest).map (fun C => C.image f.toFun)) := hns
        rw [List.isChain_cons] at hns_cons
        obtain ⟨hrel_ns, hns_tl⟩ := hns_cons
        have hab_ns : a.image f.toFun ≠ b.image f.toFun := by
          have := hrel_ns (b.image f.toFun) rfl
          exact this

        have ha_img : a.image f.toFun = a := image_eq_of_fixes_pointwise hfix_head
        have hne_ba : b.image f.toFun ≠ a := by rw [← ha_img]; exact hab_ns.symm

        have hfix_b : ∀ v ∈ b, f.toFun v = v :=
          thin_fixes_next_chamber hthin f hf hfF hab hfix_head hne_ba

        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun D hD => hall D (List.mem_cons_of_mem a hD))
          hfix_b hns_tl C hC

/-- *Book uniqueness lemma (3.3/3.5)*, internal form: in a thin chamber complex, if $f$ is a
facet-preserving chamber map fixing $C_0$ pointwise, then along any gallery starting at $C_0$,
either the $f$-image stutters or $f$ fixes every chamber pointwise. -/
theorem uniqueness_lemma_book
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap) (hfF : f.PreservesFacets)
    (C₀ : Finset V) (_hC₀ : X.toSimplicialComplex.IsMaximal C₀)
    (hfix : ∀ v ∈ C₀, f.toFun v = v)
    (γ : Gallery X.toSimplicialComplex)
    (hstart : γ.chambers.head? = some C₀) :
    GalleryStuttersUnder γ.chambers f.toFun ∨
    FixesAllPointwise γ.chambers f.toFun := by

  by_cases hns : List.IsChain (· ≠ ·) (γ.chambers.map (fun C => C.image f.toFun))
  ·
    right
    have hne : γ.chambers ≠ [] := by
      intro h; simp [h] at hstart
    have hhead_eq : γ.chambers.head hne = C₀ := by
      rw [List.head?_eq_some_head hne] at hstart
      exact Option.some_injective _ hstart
    intro C hC v hv
    exact fixes_along_chain_of_nonstuttering hthin f hf hfF
      γ.chambers hne γ.adjacent_consecutive γ.all_maximal
      (hhead_eq ▸ hfix) hns C hC v hv
  ·
    left
    exact hns

/-- Variant of `thin_fixes_next_chamber` not requiring `PreservesFacets` — the facet property of
$f(C_2)$ is derived from cardinalities. -/
lemma thin_fixes_next_chamber_no_pfacets
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap)
    {C₁ C₂ : Finset V}
    (hadj : X.toSimplicialComplex.Adjacent C₁ C₂)
    (hfix₁ : ∀ v ∈ C₁, f.toFun v = v)
    (hne : C₂.image f.toFun ≠ C₁) :
    ∀ v ∈ C₂, f.toFun v = v := by
  obtain ⟨hC₁max, hC₂max, hC₁C₂, F, hFC₁, hFC₂⟩ := hadj

  have hF_sub_C₁ : F ⊆ C₁ := hFC₁.1.2.2
  have hfixF : ∀ v ∈ F, f.toFun v = v := fun v hv => hfix₁ v (hF_sub_C₁ hv)

  have hF_sub_C₂ : F ⊆ C₂ := hFC₂.1.2.2

  have hF_sub_fC₂ : F ⊆ C₂.image f.toFun := by
    intro v hv
    simp only [Finset.mem_image]
    exact ⟨v, hF_sub_C₂ hv, hfixF v hv⟩

  have hfC₂max : X.toSimplicialComplex.IsMaximal (C₂.image f.toFun) := hf C₂ hC₂max


  have hfC₂_facet : X.toSimplicialComplex.IsFacet F (C₂.image f.toFun) := by
    constructor
    · exact ⟨hFC₁.1.1, hfC₂max.1, hF_sub_fC₂⟩
    ·
      have h1 : (C₂ \ F).card = 1 := hFC₂.2
      have h2 : C₂.card = F.card + 1 := by
        have := Finset.card_sdiff_add_card_eq_card hF_sub_C₂; omega
      have h3 : (C₂.image f.toFun).card ≤ C₂.card := Finset.card_image_le
      have h4 : F.card ≤ (C₂.image f.toFun).card := Finset.card_le_card hF_sub_fC₂
      have h5 : (C₂.image f.toFun).card = F.card ∨
                (C₂.image f.toFun).card = F.card + 1 := by omega
      rcases h5 with h5 | h5
      ·
        exfalso
        have hfC₂_eq_F : C₂.image f.toFun = F :=
          (Finset.eq_of_subset_of_card_le hF_sub_fC₂ (by omega)).symm
        rw [hfC₂_eq_F] at hfC₂max

        have hF_ne_C₁ : F ≠ C₁ := by
          intro heq; rw [heq] at hFC₁
          have : (C₁ \ C₁).card = 1 := hFC₁.2
          simp at this
        exact hF_ne_C₁ (hfC₂max.2 C₁ hC₁max.1 hF_sub_C₁)
      ·
        have := Finset.card_sdiff_add_card_eq_card hF_sub_fC₂; omega

  have hthin_inst := hthin F C₁ hFC₁ hC₁max
  obtain ⟨D, ⟨hDC₁, hFD, hDmax⟩, huniq⟩ := hthin_inst

  have hC₂_eq_D : C₂ = D := huniq C₂ ⟨hC₁C₂.symm, hFC₂, hC₂max⟩

  have hfC₂_eq_D : C₂.image f.toFun = D :=
    huniq (C₂.image f.toFun) ⟨hne, hfC₂_facet, hfC₂max⟩

  have hC₂img : C₂.image f.toFun = C₂ := by rw [hfC₂_eq_D, ← hC₂_eq_D]

  exact fixes_pointwise_of_facet_and_image hFC₂.1.2.2 hFC₂.2 hfixF hC₂img

/-- Chain variant of `thin_fixes_next_chamber_no_pfacets` — propagates pointwise fixing along a
non-stuttering chain without assuming `PreservesFacets`. -/
lemma fixes_along_chain_no_pfacets
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap)
    (cs : List (Finset V))
    (hne : cs ≠ [])
    (hchain : List.IsChain X.toSimplicialComplex.Adjacent cs)
    (hall : ∀ C ∈ cs, X.toSimplicialComplex.IsMaximal C)
    (hfix_head : ∀ v ∈ cs.head hne, f.toFun v = v)
    (hns : List.IsChain (· ≠ ·) (cs.map (fun C => C.image f.toFun))) :
    ∀ C ∈ cs, ∀ v ∈ C, f.toFun v = v := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro C hC
    rw [List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact hfix_head
    · cases tl with
      | nil => simp at hC
      | cons b rest =>

        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : X.toSimplicialComplex.Adjacent a b := hrel b rfl

        have hns_cons : List.IsChain (· ≠ ·)
            ((a.image f.toFun) :: (b :: rest).map (fun C => C.image f.toFun)) := hns
        rw [List.isChain_cons] at hns_cons
        obtain ⟨hrel_ns, hns_tl⟩ := hns_cons
        have hab_ns : a.image f.toFun ≠ b.image f.toFun := by
          have := hrel_ns (b.image f.toFun) rfl
          exact this

        have ha_img : a.image f.toFun = a := image_eq_of_fixes_pointwise hfix_head
        have hne_ba : b.image f.toFun ≠ a := by rw [← ha_img]; exact hab_ns.symm

        have hfix_b : ∀ v ∈ b, f.toFun v = v :=
          thin_fixes_next_chamber_no_pfacets hthin f hf hab hfix_head hne_ba

        exact ih (List.cons_ne_nil b rest) hchain_tl
          (fun D hD => hall D (List.mem_cons_of_mem a hD))
          hfix_b hns_tl C hC

/-- *Uniqueness lemma* (no facet-preservation hypothesis): in a thin chamber complex, if $f$ is
a chamber map fixing $C_0$ pointwise, then along any gallery starting at $C_0$, either $f$'s
image stutters or $f$ fixes every chamber of the gallery pointwise. -/
theorem uniqueness_lemma
    {X : ChamberComplex V}
    (hthin : X.IsThin)
    (f : Morphism X.toSimplicialComplex X.toSimplicialComplex)
    (hf : f.IsChamberMap)
    (C₀ : Finset V) (_hC₀ : X.toSimplicialComplex.IsMaximal C₀)
    (hfix : ∀ v ∈ C₀, f.toFun v = v)
    (γ : Gallery X.toSimplicialComplex)
    (hstart : γ.chambers.head? = some C₀) :
    GalleryStuttersUnder γ.chambers f.toFun ∨
    FixesAllPointwise γ.chambers f.toFun := by

  by_cases hns : List.IsChain (· ≠ ·) (γ.chambers.map (fun C => C.image f.toFun))
  ·
    right
    have hne : γ.chambers ≠ [] := by
      intro h; simp [h] at hstart
    have hhead_eq : γ.chambers.head hne = C₀ := by
      rw [List.head?_eq_some_head hne] at hstart
      exact Option.some_injective _ hstart
    intro C hC v hv
    exact fixes_along_chain_no_pfacets hthin f hf
      γ.chambers hne γ.adjacent_consecutive γ.all_maximal
      (hhead_eq ▸ hfix) hns C hC v hv
  ·
    left
    exact hns

end SimplicialComplex
