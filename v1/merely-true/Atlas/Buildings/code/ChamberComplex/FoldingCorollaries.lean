/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.GalleryTypes.ThinFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.WallCrossing
import Atlas.Buildings.code.ChamberComplex.GalleryConcatenation

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- Symmetry of chamber adjacency (local alias). -/
lemma adjacent_symm' {K : SimplicialComplex V} {C D : Finset V}
    (h : K.Adjacent C D) : K.Adjacent D C := by
  obtain ⟨hC, hD, hne, F, hFC, hFD⟩ := h
  exact ⟨hD, hC, Ne.symm hne, F, hFD, hFC⟩

/-- Idempotence at the chamber level: $f(f(C)) = f(C)$ for any chamber $C$. -/
lemma image_is_fixed' (K : ChamberComplex V) (f : Folding K) (C : Finset V)
    (hC : K.toSimplicialComplex.IsMaximal C) :
    (C.image f.morph.toFun).image f.morph.toFun = C.image f.morph.toFun := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (f.idempotent u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f.morph.toFun u, ⟨u, hu, rfl⟩, f.idempotent u⟩

/-- A folding maps an adjacent pair either to the same chamber (stutter) or to an adjacent pair. -/
lemma folding_maps_adj' (K : ChamberComplex V) (f : Folding K)
    (C D : Finset V) (hadj : K.toSimplicialComplex.Adjacent C D) :
    C.image f.morph.toFun = D.image f.morph.toFun ∨
    K.toSimplicialComplex.Adjacent (C.image f.morph.toFun) (D.image f.morph.toFun) := by
  by_cases h : C.image f.morph.toFun = D.image f.morph.toFun
  · exact Or.inl h
  · right
    have hCmax := f.chamberMap C hadj.1
    have hDmax := f.chamberMap D hadj.2.1
    obtain ⟨F, hFC, hFD⟩ := hadj.2.2.2
    have hFF := f.preservesFacets F C hFC
    have hFD' := f.preservesFacets F D hFD
    exact ⟨hCmax, hDmax, h, F.image f.morph.toFun, hFF, hFD'⟩

/-- Any connecting gallery bounds the gallery distance from above: $d(C,D) \leq \ell(g)$. -/
lemma galleryDist_le_length' {K : SimplicialComplex V}
    (C D : Finset V) (g : Gallery K) (hconn : g.Connects C D) :
    galleryDist K C D ≤ g.length := by
  by_cases h : C = D
  · subst h; simp [galleryDist]
  · unfold galleryDist
    simp only [h, ↓reduceIte]
    exact Nat.sInf_le ⟨g, hconn, rfl⟩

/-- If two chambers have gallery distance $0$, they must be equal. -/
lemma galleryDist_eq_zero_imp (K : ChamberComplex V)
    (C D : Finset V)
    (hCmax : K.toSimplicialComplex.IsMaximal C)
    (hDmax : K.toSimplicialComplex.IsMaximal D)
    (h : galleryDist K.toSimplicialComplex C D = 0) : C = D := by
  by_contra hne
  unfold galleryDist at h
  simp only [hne, ↓reduceIte] at h
  obtain ⟨g, hg⟩ := K.gallery_connected C D hCmax hDmax
  have hnonempty : {n | ∃ g : Gallery K.toSimplicialComplex, g.Connects C D ∧ g.length = n}.Nonempty :=
    ⟨g.length, g, ⟨hg.1, hg.2⟩, rfl⟩
  rw [Nat.sInf_eq_zero] at h
  rcases h with ⟨g0, hconn0, hlen0⟩ | hempty
  ·
    have hne_nil := Gallery.chambers_ne_nil g0
    have hcl : g0.chambers.length = 1 := by
      have := g0.length_pos; unfold Gallery.length at hlen0; omega

    have hhead := hconn0.1
    have hlast := hconn0.2
    have : g0.chambers.head hne_nil = g0.chambers.getLast hne_nil := by
      have hone : ∃ x, g0.chambers = [x] := by
        match g0.chambers, hcl with
        | [x], _ => exact ⟨x, rfl⟩
      obtain ⟨x, hx⟩ := hone
      simp [hx]
    rw [List.head?_eq_some_head hne_nil] at hhead
    rw [List.getLast?_eq_some_getLast hne_nil] at hlast
    have hCeq := Option.some_injective _ hhead
    have hDeq := Option.some_injective _ hlast
    exact hne (hCeq.symm.trans (this ▸ hDeq))
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hnonempty)

/-- Adjacent chambers admit a gallery of length $1$ connecting them. -/
lemma exists_gallery_adj {K : SimplicialComplex V} {C D : Finset V}
    (hadj : K.Adjacent C D) :
    ∃ g : Gallery K, g.Connects C D ∧ g.length = 1 := by
  have hchain : List.IsChain K.Adjacent [C, D] := by
    constructor; exact hadj; exact List.isChain_singleton D
  refine ⟨⟨[C, D], by simp, ?_, hchain⟩, ?_, ?_⟩
  · intro X hX
    simp [List.mem_cons, List.mem_singleton] at hX
    rcases hX with rfl | rfl <;> [exact hadj.1; exact hadj.2.1]
  · exact ⟨rfl, rfl⟩
  · rfl

/-- Drop the first chamber of a positive-length gallery to obtain a shorter gallery starting at
the second chamber. -/
lemma gallery_drop_first {K : SimplicialComplex V}
    (g : Gallery K) (C D : Finset V) (hconn : g.Connects C D)
    (hlen : g.length ≥ 1) :
    ∃ C₁ : Finset V, ∃ g' : Gallery K,
      g'.Connects C₁ D ∧
      g'.length = g.length - 1 ∧
      K.Adjacent C C₁ ∧
      C₁ ∈ g.chambers ∧
      (∀ X, X ∈ g'.chambers → X ∈ g.chambers) := by
  have hne := Gallery.chambers_ne_nil g

  have hclen : g.chambers.length ≥ 2 := by
    unfold Gallery.length at hlen; omega

  have hhead : g.chambers.head hne = C := by
    have := hconn.1
    rw [List.head?_eq_some_head hne] at this
    exact Option.some_injective _ this
  have hcons : g.chambers = C :: g.chambers.tail := by
    rw [← hhead]; exact (List.cons_head_tail hne).symm
  have htail_ne : g.chambers.tail ≠ [] := by
    intro h; rw [hcons] at hclen; simp [h] at hclen
  let C₁ := g.chambers.tail.head htail_ne
  have htail_pos : g.chambers.tail.length > 0 := List.length_pos_of_ne_nil htail_ne

  have hall_tail : ∀ X ∈ g.chambers.tail, K.IsMaximal X := by
    intro X hX; exact g.all_maximal X (List.mem_of_mem_tail hX)

  have hchain_tail : List.IsChain K.Adjacent g.chambers.tail :=
    g.adjacent_consecutive.tail

  let g' : Gallery K := {
    chambers := g.chambers.tail
    length_pos := htail_pos
    all_maximal := hall_tail
    adjacent_consecutive := hchain_tail
  }

  have hconn' : g'.Connects C₁ D := by
    constructor
    · show g.chambers.tail.head? = some C₁
      exact List.head?_eq_head htail_ne
    · show g.chambers.tail.getLast? = some D
      have : g.chambers.tail.getLast? = g.chambers.getLast? := by
        rw [hcons]
        simp [List.getLast?_cons]
        rw [List.getLast?_eq_some_getLast htail_ne]
        simp
      rw [this]; exact hconn.2

  have hlen' : g'.length = g.length - 1 := by
    unfold Gallery.length
    show g.chambers.tail.length - 1 = g.chambers.length - 1 - 1
    rw [hcons]; simp [List.length_cons]

  have hadj : K.Adjacent C C₁ := by
    have hchain_full := g.adjacent_consecutive
    rw [hcons] at hchain_full
    have : List.IsChain K.Adjacent (C :: g.chambers.tail) := hchain_full
    exact this.rel_head? (List.head?_eq_head htail_ne ▸ rfl)

  have hC₁mem : C₁ ∈ g.chambers := by
    rw [hcons]; exact List.mem_cons.mpr (Or.inr (List.head_mem htail_ne))

  have hsub : ∀ X, X ∈ g'.chambers → X ∈ g.chambers := by
    intro X hX; exact List.mem_of_mem_tail hX
  exact ⟨C₁, g', hconn', hlen', hadj, hC₁mem, hsub⟩

/-- Key folding inequality: if $f$ fixes $D$ but moves $E$, then $d(f(E), D) < d(E, D)$ —
i.e. folding strictly decreases gallery distance to a fixed chamber. -/
theorem folding_shortens_dist
    (K : ChamberComplex V) (f : Folding K) (D E : Finset V)
    (hDmax : K.toSimplicialComplex.IsMaximal D)
    (hEmax : K.toSimplicialComplex.IsMaximal E)
    (hfD : D.image f.morph.toFun = D)
    (hfE : E.image f.morph.toFun ≠ E) :
    galleryDist K.toSimplicialComplex (E.image f.morph.toFun) D <
      galleryDist K.toSimplicialComplex E D := by

  have hED : E ≠ D := by intro h; subst h; exact hfE hfD

  have hfE_fixed := Folding.image_is_fixed f hEmax
  have hfE_max : K.toSimplicialComplex.IsMaximal (E.image f.morph.toFun) := hfE_fixed.1
  have hfE_eq : (E.image f.morph.toFun).image f.morph.toFun = E.image f.morph.toFun := hfE_fixed.2

  suffices key : ∀ n, ∀ E' : Finset V,
      K.toSimplicialComplex.IsMaximal E' →
      E'.image f.morph.toFun ≠ E' →
      galleryDist K.toSimplicialComplex E' D = n →
      galleryDist K.toSimplicialComplex (E'.image f.morph.toFun) D < n by
    exact key (galleryDist K.toSimplicialComplex E D) E hEmax hfE rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro E' hE'max hE'moved hn

    have hE'D : E' ≠ D := by intro h; subst h; exact hE'moved hfD
    have hn_pos : n ≥ 1 := by
      by_contra h; push_neg at h
      have : n = 0 := by omega
      subst this
      exact hE'D (galleryDist_eq_zero_imp K E' D hE'max hDmax hn)

    have hset_ne : {m | ∃ g : Gallery K.toSimplicialComplex,
        g.Connects E' D ∧ g.length = m}.Nonempty := by
      obtain ⟨g, hg⟩ := K.gallery_connected E' D hE'max hDmax
      exact ⟨g.length, g, ⟨hg.1, hg.2⟩, rfl⟩
    have hmin_mem : n ∈ {m | ∃ g : Gallery K.toSimplicialComplex,
        g.Connects E' D ∧ g.length = m} := by
      rw [← hn]; unfold galleryDist; simp only [hE'D, ↓reduceIte]
      exact Nat.sInf_mem hset_ne
    obtain ⟨γ, hγconn, hγlen⟩ := hmin_mem

    obtain ⟨C₁, γ', hγ'conn, hγ'len, hadj_E'C₁, hC₁mem, hsub⟩ :=
      gallery_drop_first γ E' D hγconn (by omega)

    have hC₁max : K.toSimplicialComplex.IsMaximal C₁ := γ.all_maximal C₁ hC₁mem

    have hC₁_dist : galleryDist K.toSimplicialComplex C₁ D ≤ n - 1 := by
      calc galleryDist K.toSimplicialComplex C₁ D
          ≤ γ'.length := galleryDist_le_length' C₁ D γ' hγ'conn
        _ = γ.length - 1 := hγ'len
        _ = n - 1 := by omega

    by_cases hC₁fixed : C₁.image f.morph.toFun = C₁
    ·

      have hadj_symm : K.toSimplicialComplex.Adjacent C₁ E' := adjacent_symm' hadj_E'C₁
      have hfE'_eq_C₁ : E'.image f.morph.toFun = C₁ :=
        f.stutter_at_boundary C₁ E' hadj_symm ⟨hC₁max, hC₁fixed⟩ hE'moved

      rw [hfE'_eq_C₁]
      exact Nat.lt_of_le_of_lt hC₁_dist (by omega)
    ·

      have hC₁_dist_n : galleryDist K.toSimplicialComplex C₁ D ≤ n - 1 := hC₁_dist
      have hC₁_dist_lt_n : galleryDist K.toSimplicialComplex C₁ D < n := by omega
      have hIH := ih (galleryDist K.toSimplicialComplex C₁ D)
        hC₁_dist_lt_n C₁ hC₁max hC₁fixed rfl

      have hfC₁_dist : galleryDist K.toSimplicialComplex (C₁.image f.morph.toFun) D ≤ n - 2 := by
        omega

      have hfC₁max : K.toSimplicialComplex.IsMaximal (C₁.image f.morph.toFun) :=
        (Folding.image_is_fixed f hC₁max).1

      have hadj_image := folding_maps_adj' K f E' C₁ hadj_E'C₁
      rcases hadj_image with heq | hadj_fE'fC₁
      ·
        rw [heq]
        exact Nat.lt_of_le_of_lt hfC₁_dist (by omega)
      ·


        have hfE'max : K.toSimplicialComplex.IsMaximal (E'.image f.morph.toFun) :=
          (Folding.image_is_fixed f hE'max).1

        obtain ⟨g_adj, hg_adj_conn, hg_adj_len⟩ := exists_gallery_adj hadj_fE'fC₁

        by_cases hfC₁D : C₁.image f.morph.toFun = D
        ·
          have hconn_fE'D : g_adj.Connects (E'.image f.morph.toFun) D := by
            rw [← hfC₁D]; exact hg_adj_conn
          calc galleryDist K.toSimplicialComplex (E'.image f.morph.toFun) D
              ≤ g_adj.length := galleryDist_le_length' _ _ g_adj hconn_fE'D
            _ = 1 := hg_adj_len
            _ ≤ n - 1 := by omega
            _ < n := by omega
        ·
          have hset_ne_fC₁ : {m | ∃ g : Gallery K.toSimplicialComplex,
              g.Connects (C₁.image f.morph.toFun) D ∧ g.length = m}.Nonempty := by
            obtain ⟨g, hg⟩ := K.gallery_connected (C₁.image f.morph.toFun) D hfC₁max hDmax
            exact ⟨g.length, g, ⟨hg.1, hg.2⟩, rfl⟩
          have hmin_fC₁ : galleryDist K.toSimplicialComplex (C₁.image f.morph.toFun) D ∈
              {m | ∃ g : Gallery K.toSimplicialComplex,
                g.Connects (C₁.image f.morph.toFun) D ∧ g.length = m} := by
            unfold galleryDist; simp only [hfC₁D, ↓reduceIte]
            exact Nat.sInf_mem hset_ne_fC₁
          obtain ⟨g_fC₁D, hg_fC₁D_conn, hg_fC₁D_len⟩ := hmin_fC₁

          obtain ⟨g_concat, hg_concat_conn, hg_concat_len, _⟩ :=
            Gallery.gallery_concat (E'.image f.morph.toFun) (C₁.image f.morph.toFun) D
              g_adj g_fC₁D hg_adj_conn hg_fC₁D_conn
          calc galleryDist K.toSimplicialComplex (E'.image f.morph.toFun) D
              ≤ g_concat.length := galleryDist_le_length' _ _ g_concat hg_concat_conn
            _ = g_adj.length + g_fC₁D.length := hg_concat_len
            _ = 1 + galleryDist K.toSimplicialComplex (C₁.image f.morph.toFun) D := by
                rw [hg_adj_len, hg_fC₁D_len]
            _ ≤ 1 + (n - 2) := by omega
            _ < n := by omega

/-- Characterization of the half-apartment via gallery distance: for a reversible folding $f$
with adjacent boundary pair $C$ (fixed) and $C'$ (moved), the fixed half is exactly
$\{D \text{ chamber} \mid d(C,D) < d(C',D)\}$. -/
theorem HalfApartmentDistChar
    (K : ChamberComplex V) (rf : ReversibleFolding K)
    (C C' : Finset V)
    (hadj : K.toSimplicialComplex.Adjacent C C')
    (hC_fixed : C ∈ rf.f.fixedChambers)
    (hC'_moved : C' ∈ rf.f.movedChambers) :
    rf.f.fixedChambers = { D | K.toSimplicialComplex.IsMaximal D ∧
      galleryDist K.toSimplicialComplex C D <
      galleryDist K.toSimplicialComplex C' D } := by

  have hCmax : K.toSimplicialComplex.IsMaximal C := hC_fixed.1
  have hC'max : K.toSimplicialComplex.IsMaximal C' := hC'_moved.1
  have hCC' : C ≠ C' := by
    intro h; subst h; exact hC'_moved.2 hC_fixed.2


  have hfC' : C'.image rf.f.morph.toFun = C :=
    rf.f.stutter_at_boundary C C' hadj ⟨hCmax, hC_fixed.2⟩ hC'_moved.2
  ext D
  simp only [Set.mem_setOf_eq, Folding.fixedChambers]
  constructor
  ·
    intro ⟨hDmax, hfD⟩
    refine ⟨hDmax, ?_⟩
    have h := folding_shortens_dist K rf.f D C' hDmax hC'max hfD hC'_moved.2
    rwa [hfC'] at h
  ·
    intro ⟨hDmax, hlt⟩
    refine ⟨hDmax, ?_⟩
    by_contra hfD_ne
    have hD_moved : D ∈ rf.f.movedChambers := ⟨hDmax, hfD_ne⟩
    have hD_fixed_g : D ∈ rf.g.fixedChambers := by rwa [← rf.complementary_moved]
    have hC_moved_g : C ∈ rf.g.movedChambers := by rwa [← rf.complementary_fixed]
    have h := folding_shortens_dist K rf.g D C hDmax hCmax hD_fixed_g.2 hC_moved_g.2
    have hgC : C.image rf.g.morph.toFun = C' :=
      rf.opposite_action C C' hCmax hC'max hCC' hC_fixed.2 hfC'
    rw [hgC] at h
    exact Nat.lt_asymm h hlt

end ChamberComplex
