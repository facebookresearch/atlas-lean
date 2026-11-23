/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Spherical
import Atlas.Buildings.code.Building.Convexity
import Atlas.Buildings.code.Building.OppositeChambers
import Atlas.Buildings.code.ChamberComplex.FoldingCorollaries
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.Set.Finite.List

variable {V : Type*} [DecidableEq V]

/-- A simplicial complex has *finite diameter* bounded by $d$ if every pair
of chambers has gallery distance at most $d$. -/
def SimplicialComplex.HasFiniteDiameter (K : SimplicialComplex V) (d : ℕ) : Prop :=
  ∀ C D, K.IsMaximal C → K.IsMaximal D → galleryDist K C D ≤ d

/-- A building has *finite diameter* if its underlying chamber complex does. -/
def Building.HasFiniteDiameter (b : Building V) (d : ℕ) : Prop :=
  b.toChamberComplex.toSimplicialComplex.HasFiniteDiameter d

/-- A length bound for words in a Coxeter group: the length of any
representation of $w$ is bounded by the diameter. -/
lemma chain_word_bound {W : Type*} [Group W] {B : Type*}
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (l : List W) (hne : l ≠ [])
    (h_chain : List.IsChain (fun w w' => ∃ i : B, w' = w * cs.simple i) l) :
    cs.length ((l.head hne)⁻¹ * l.getLast hne) ≤ l.length - 1 := by
  induction h_chain with
  | nil => exact absurd rfl hne
  | singleton a =>
    simp [inv_mul_cancel]
  | @cons_cons a b l' hab htl ih =>
    have htl_ne : (b :: l') ≠ [] := List.cons_ne_nil b l'
    have ih' := ih htl_ne
    obtain ⟨i, hi⟩ := hab
    simp only [List.head_cons] at ih' ⊢
    set x := (b :: l').getLast htl_ne with hx_def
    have h_last : (a :: b :: l').getLast hne = x := by
      rw [hx_def]; exact List.getLast_cons (h := htl_ne)
    rw [h_last]
    have hab_eq : a⁻¹ * b = cs.simple i := by rw [hi]; group
    have key : a⁻¹ * x = cs.simple i * (b⁻¹ * x) := by
      rw [← hab_eq]; group
    rw [key]
    calc cs.length (cs.simple i * (b⁻¹ * x))
        ≤ cs.length (cs.simple i) + cs.length (b⁻¹ * x) :=
          cs.length_mul_le _ _
      _ = 1 + cs.length (b⁻¹ * x) := by rw [cs.length_simple]
      _ ≤ 1 + ((b :: l').length - 1) := by linarith
      _ = (a :: b :: l').length - 1 := by simp; omega

/-- Pushforward of a chain under a relation-respecting map. -/
lemma ischain_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} {f : α → β}
    (hRS : ∀ a b, R a b → S (f a) (f b))
    {l : List α} (h : List.IsChain R l) :
    List.IsChain S (l.map f) := by
  induction h with
  | nil => exact .nil
  | singleton a => exact .singleton _
  | cons_cons hab htl ih => exact .cons_cons (hRS _ _ hab) ih

/-- The Coxeter length of any word is at most the gallery distance between
the corresponding chambers. -/
theorem word_length_le_galleryDist
    {V : Type*} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V)
    (hcc : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (_hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :
    ∀ C D, A.IsMaximal C → A.IsMaximal D →
      M.toCoxeterSystem.length ((φ C)⁻¹ * φ D) ≤ galleryDist A C D := by
  intro C D hC hD
  by_cases hCD : C = D
  · subst hCD
    simp only [inv_mul_cancel, galleryDist_self]
    exact le_of_eq M.toCoxeterSystem.length_one
  · unfold galleryDist
    rw [if_neg hCD]
    apply le_csInf
    · have ⟨g₀, hconn₀⟩ := cc.gallery_connected C D (hcc ▸ hC) (hcc ▸ hD)
      let g : Gallery A := {
        chambers := g₀.chambers
        length_pos := g₀.length_pos
        all_maximal := fun C' hC' => hcc ▸ g₀.all_maximal C' hC'
        adjacent_consecutive := hcc ▸ g₀.adjacent_consecutive
      }
      exact ⟨g.length, g, ⟨hconn₀.1, hconn₀.2⟩, rfl⟩
    · intro n ⟨g, hconn, hlen⟩
      rw [← hlen]
      let cs := M.toCoxeterSystem
      have hne : g.chambers ≠ [] := by
        intro h; have := g.length_pos; rw [h] at this; simp at this
      have h_adj_impl : ∀ a b, A.Adjacent a b →
          (∃ i : B_idx, φ b = φ a * cs.simple i) := by
        intro a b hadj; exact (_hφ_adj a b hadj).2
      have h_chain_φ : List.IsChain
          (fun w w' => ∃ i : B_idx, w' = w * cs.simple i)
          (g.chambers.map φ) :=
        ischain_map h_adj_impl g.adjacent_consecutive
      have hne_map : g.chambers.map φ ≠ [] := by simp [hne]
      have h_bound := chain_word_bound cs (g.chambers.map φ) hne_map h_chain_φ
      rw [List.head_map, List.getLast_map] at h_bound
      have h_head : g.chambers.head hne = C := by
        have := hconn.1; rw [List.head?_eq_some_head hne] at this
        exact Option.some.inj this
      have h_last : g.chambers.getLast hne = D := by
        have := hconn.2; rw [List.getLast?_eq_some_getLast hne] at this
        exact Option.some.inj this
      rw [h_head, h_last] at h_bound
      unfold Gallery.length
      calc cs.length ((φ C)⁻¹ * φ D)
          ≤ (g.chambers.map φ).length - 1 := h_bound
        _ = g.chambers.length - 1 := by simp

open scoped Classical in
/-- A Coxeter complex of finite diameter is finite (has finitely many
chambers). -/
theorem coxeter_complex_finite_diameter_implies_finite
    {V : Type*} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) [Fintype B_idx] (M : CoxeterMatrix B_idx) (cc : ChamberComplex V)
    (hcc : cc.toSimplicialComplex = A)
    (d : ℕ)
    (hd : A.HasFiniteDiameter d)

    (φ : Finset V → M.Group)
    (hφ_inj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hφ_surj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :
    Set.Finite A.faces := by


  haveI : DecidableEq B_idx := Classical.decEq B_idx

  have h_wl_le_gd := word_length_le_galleryDist A B_idx M cc hcc φ hφ_adj

  have h_wl_bd : ∀ w : M.Group, M.toCoxeterSystem.length w ≤ d := by
    intro w
    obtain ⟨C₀, hC₀_max, hC₀_eq⟩ := hφ_surj 1
    obtain ⟨D, hD_max, hD_eq⟩ := hφ_surj w
    calc M.toCoxeterSystem.length w
        = M.toCoxeterSystem.length ((φ C₀)⁻¹ * φ D) := by simp [hC₀_eq, hD_eq]
      _ ≤ galleryDist A C₀ D := h_wl_le_gd C₀ D hC₀_max hD_max
      _ ≤ d := hd C₀ D hC₀_max hD_max


  have h_group_finite : Set.Finite (Set.univ : Set M.Group) := by

    let cs := M.toCoxeterSystem
    have h_surj : ∀ w : M.Group, ∃ ω : List B_idx, ω.length ≤ d ∧ cs.wordProd ω = w := by
      intro w
      obtain ⟨ω, hω_red, hω_eq⟩ := cs.exists_isReduced w
      refine ⟨ω, ?_, hω_eq.symm⟩
      calc ω.length = cs.length (cs.wordProd ω) := hω_red.eq.symm
        _ = cs.length w := by rw [← hω_eq]
        _ ≤ d := h_wl_bd w

    have h_fin_lists : Set.Finite {ω : List B_idx | ω.length ≤ d} :=
      List.finite_length_le B_idx d

    exact Set.Finite.subset (h_fin_lists.image cs.wordProd) (fun w _ =>
      let ⟨ω, hlen, heq⟩ := h_surj w; ⟨ω, hlen, heq⟩)

  have h_chambers_finite : Set.Finite {C : Finset V | A.IsMaximal C} := by
    have h_inj_φ : Set.InjOn φ {C : Finset V | A.IsMaximal C} :=
      fun C hC D hD heq => hφ_inj C hC D hD heq
    exact Set.Finite.of_finite_image
      (Set.Finite.subset h_group_finite (Set.subset_univ _)) h_inj_φ

  have h_faces_sub : A.faces ⊆ ⋃ C ∈ {C | A.IsMaximal C}, {σ | σ ⊆ C ∧ σ.Nonempty} := by
    intro σ hσ
    have hσ_cc : σ ∈ cc.toSimplicialComplex.faces := hcc ▸ hσ
    obtain ⟨C, hC_max, hσ_sub⟩ := cc.exists_maximal σ hσ_cc
    have hC_max_A : A.IsMaximal C := hcc ▸ hC_max
    exact Set.mem_biUnion hC_max_A ⟨hσ_sub, A.nonempty_of_mem σ hσ⟩
  apply Set.Finite.subset _ h_faces_sub
  apply Set.Finite.biUnion h_chambers_finite
  intro C hC
  apply Set.Finite.subset (Set.toFinite (↑C.powerset : Set (Finset V)))
  intro σ ⟨hsub, _⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr hsub)




/-- Adjacency in a chamber subcomplex transfers to adjacency in the
ambient complex. -/
theorem adjacent_in_subcomplex'
    {V : Type*} [DecidableEq V]
    {A K : SimplicialComplex V} (_hsub : IsSubcomplex A K)
    {C D : Finset V} (hadj : K.Adjacent C D)
    (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    A.Adjacent C D := by
  obtain ⟨_, _, hne, F, hFC, hFD⟩ := hadj
  have hF_ne : F.Nonempty := K.nonempty_of_mem _ hFC.1.1
  have hF_A : F ∈ A.faces := A.down_closed hC.1 hFC.1.2.2 hF_ne
  exact ⟨hC, hD, hne, F, ⟨⟨hF_A, hC.1, hFC.1.2.2⟩, hFC.2⟩, ⟨⟨hF_A, hD.1, hFD.1.2.2⟩, hFD.2⟩⟩

/-- A gallery in a subcomplex remains a gallery in the ambient complex. -/
theorem chain_transfer_to_subcomplex'
    {V : Type*} [DecidableEq V]
    {A K : SimplicialComplex V} (hsub : IsSubcomplex A K)
    (l : List (Finset V))
    (hchain : List.IsChain K.Adjacent l)
    (hmax : ∀ E ∈ l, A.IsMaximal E) :
    List.IsChain A.Adjacent l := by
  induction hchain with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.IsChain.singleton a
  | cons_cons hab htail ih =>
    apply List.IsChain.cons_cons
    · exact adjacent_in_subcomplex' hsub hab
        (hmax _ List.mem_cons_self)
        (hmax _ (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
    · exact ih (fun E hE => hmax E (List.mem_cons.mpr (Or.inr hE)))

/-- Adjacency in a complex lifts to adjacency in a supercomplex containing
both chambers. -/
theorem adjacent_lift_to_supercomplex
    {V : Type*} [DecidableEq V]
    {A K : SimplicialComplex V} (hsub : IsSubcomplex A K)
    {C D : Finset V} (hadj : A.Adjacent C D)
    (hC_K : K.IsMaximal C) (hD_K : K.IsMaximal D) :
    K.Adjacent C D := by
  obtain ⟨_, _, hne, F, hFC, hFD⟩ := hadj
  exact ⟨hC_K, hD_K, hne, F,
    ⟨⟨hsub hFC.1.1, hC_K.1, hFC.1.2.2⟩, hFC.2⟩,
    ⟨⟨hsub hFD.1.1, hD_K.1, hFD.1.2.2⟩, hFD.2⟩⟩

/-- A chain (gallery) in a complex lifts to the same chain in a
supercomplex. -/
theorem chain_lift_to_supercomplex
    {V : Type*} [DecidableEq V]
    {A K : SimplicialComplex V} (hsub : IsSubcomplex A K)
    (l : List (Finset V))
    (hchain : List.IsChain A.Adjacent l)
    (hmax_K : ∀ E ∈ l, K.IsMaximal E) :
    List.IsChain K.Adjacent l := by
  induction hchain with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.IsChain.singleton a
  | cons_cons hab htail ih =>
    apply List.IsChain.cons_cons
    · exact adjacent_lift_to_supercomplex hsub hab
        (hmax_K _ List.mem_cons_self)
        (hmax_K _ (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
    · exact ih (fun E hE => hmax_K E (List.mem_cons.mpr (Or.inr hE)))

/-- The gallery distance between chambers of an apartment $A$ equals the
gallery distance computed in the ambient building. -/
theorem ApartmentSystem.apt_dist_eq_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} (𝒜 : ApartmentSystem K) :
    ∀ A ∈ 𝒜.apartments,
      ∀ C D : Finset V,
        C ∈ A.faces → D ∈ A.faces →
        A.IsMaximal C → A.IsMaximal D →
        galleryDist A C D = galleryDist K.toSimplicialComplex C D := by
  intro A hA C D hC_face hD_face hC_max hD_max
  apply le_antisymm
  ·

    by_cases hCD : C = D
    · subst hCD; simp [galleryDist]
    · have hC_K := 𝒜.maximal_in_apt_is_maximal A hA C hC_max
      have hD_K := 𝒜.maximal_in_apt_is_maximal A hA D hD_max
      obtain ⟨gK, hgK_conn⟩ := K.gallery_connected C D hC_K hD_K
      have hne_K : {n | ∃ g : Gallery K.toSimplicialComplex,
          g.Connects C D ∧ g.length = n}.Nonempty :=
        ⟨gK.length, gK, ⟨hgK_conn.1, hgK_conn.2⟩, rfl⟩
      have hgd_K : galleryDist K.toSimplicialComplex C D =
          sInf {n | ∃ g : Gallery K.toSimplicialComplex,
            g.Connects C D ∧ g.length = n} := by
        unfold galleryDist; simp [hCD]
      have hmem := Nat.sInf_mem hne_K
      obtain ⟨g₀, hg₀_conn, hg₀_len⟩ := hmem
      have hg₀_min : g₀.length = galleryDist K.toSimplicialComplex C D := by
        rw [hgd_K, hg₀_len]

      have hg₀_in_A : ∀ E ∈ g₀.chambers, E ∈ A.faces :=
        𝒜.gallery_convex A hA C D hC_face hC_K hD_face hD_K g₀ hg₀_conn hg₀_min
      have hg₀_A_max : ∀ E ∈ g₀.chambers, A.IsMaximal E := fun E hE =>
        𝒜.building_maximal_in_apt_is_apt_maximal A hA E (hg₀_in_A E hE) (g₀.all_maximal E hE)
      have hsub := 𝒜.sub A hA
      have hg₀_A_chain : List.IsChain A.Adjacent g₀.chambers :=
        chain_transfer_to_subcomplex' hsub g₀.chambers g₀.adjacent_consecutive hg₀_A_max
      let gA : Gallery A :=
        ⟨g₀.chambers, g₀.length_pos, hg₀_A_max, hg₀_A_chain⟩
      calc galleryDist A C D
          ≤ gA.length := by
            unfold galleryDist; simp [hCD]
            exact Nat.sInf_le ⟨gA, hg₀_conn, rfl⟩
        _ = galleryDist K.toSimplicialComplex C D := hg₀_min
  ·

    by_cases hCD : C = D
    · subst hCD; simp [galleryDist]
    · have hC_K := 𝒜.maximal_in_apt_is_maximal A hA C hC_max
      have hD_K := 𝒜.maximal_in_apt_is_maximal A hA D hD_max
      have hsub := 𝒜.sub A hA

      obtain ⟨_, _, ccA, hccA, _⟩ := 𝒜.apt_is_coxeter A hA
      have hC_cc : ccA.toSimplicialComplex.IsMaximal C := hccA ▸ hC_max
      have hD_cc : ccA.toSimplicialComplex.IsMaximal D := hccA ▸ hD_max
      obtain ⟨gA_cc, hgA_conn⟩ := ccA.gallery_connected C D hC_cc hD_cc

      have hgA_max : ∀ E ∈ gA_cc.chambers, A.IsMaximal E := by
        intro E hE; have := gA_cc.all_maximal E hE; rwa [hccA] at this
      have hAdj_eq : ccA.toSimplicialComplex.Adjacent = A.Adjacent := by
        rw [hccA]
      have hgA_chain : List.IsChain A.Adjacent gA_cc.chambers :=
        hAdj_eq ▸ gA_cc.adjacent_consecutive

      have hne_A : {n | ∃ g : Gallery A, g.Connects C D ∧ g.length = n}.Nonempty :=
        ⟨_, ⟨⟨gA_cc.chambers, gA_cc.length_pos, hgA_max, hgA_chain⟩, hgA_conn, rfl⟩⟩

      have hgd_A : galleryDist A C D =
          sInf {n | ∃ g : Gallery A, g.Connects C D ∧ g.length = n} := by
        unfold galleryDist; simp [hCD]
      have hmem_A := Nat.sInf_mem hne_A
      obtain ⟨gA, hgA_conn_opt, hgA_len⟩ := hmem_A

      have hgA_K_max : ∀ E ∈ gA.chambers, K.toSimplicialComplex.IsMaximal E :=
        fun E hE => 𝒜.maximal_in_apt_is_maximal A hA E (gA.all_maximal E hE)
      have hgA_K_chain : List.IsChain K.toSimplicialComplex.Adjacent gA.chambers :=
        chain_lift_to_supercomplex hsub gA.chambers gA.adjacent_consecutive hgA_K_max
      let gK : Gallery K.toSimplicialComplex :=
        ⟨gA.chambers, gA.length_pos, hgA_K_max, hgA_K_chain⟩

      have hgK_len_eq : gK.length = gA.length := rfl
      calc galleryDist K.toSimplicialComplex C D
          ≤ gK.length := by
            unfold galleryDist; simp [hCD]
            exact Nat.sInf_le ⟨gK, hgA_conn_opt, rfl⟩
        _ = gA.length := hgK_len_eq
        _ = galleryDist A C D := by rw [hgd_A, hgA_len]

/-- A folding fixing $C$ strictly decreases distance to a moved chamber $D$. -/
theorem ApartmentSystem.fold_decreases_dist_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} (𝒜 : ApartmentSystem K) :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ C D : Finset V,
            cc.toSimplicialComplex.IsMaximal C →
            cc.toSimplicialComplex.IsMaximal D →
            C.image f.morph.toFun = C →
            D.image f.morph.toFun ≠ D →
            galleryDist cc.toSimplicialComplex C (D.image f.morph.toFun) <
              galleryDist cc.toSimplicialComplex C D := by
  intro A _hA cc hcc f C D hCmax hDmax hfC hfD
  rw [galleryDist_comm, galleryDist_comm cc.toSimplicialComplex C D]
  exact ChamberComplex.folding_shortens_dist cc f C D hCmax hDmax hfC hfD

/-- A folding sends maximal chambers to maximal chambers. -/
theorem ApartmentSystem.fold_preserves_maximal_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} (𝒜 : ApartmentSystem K) :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ D : Finset V,
            cc.toSimplicialComplex.IsMaximal D →
            cc.toSimplicialComplex.IsMaximal (D.image f.morph.toFun) := by
  intro A _ cc _ f D hD
  exact f.chamberMap D hD






/-- When the additive distance condition holds, a minimal gallery from $C$
to $D$ can be chosen to pass through $C'$. -/
theorem ApartmentSystem.gallery_through_chamber_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} (_𝒜 : ApartmentSystem K) :
    ∀ C C' D : Finset V,
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      K.toSimplicialComplex.IsMaximal D →
      galleryDist K.toSimplicialComplex C D =
        galleryDist K.toSimplicialComplex C C' +
        galleryDist K.toSimplicialComplex C' D →
      ∃ (g : Gallery K.toSimplicialComplex),
        g.Connects C D ∧
        g.length = galleryDist K.toSimplicialComplex C D ∧
        C' ∈ g.chambers := by
  intro C C' D hC hC' hD hdist

  have min_gallery : ∀ A B : Finset V,
      K.toSimplicialComplex.IsMaximal A → K.toSimplicialComplex.IsMaximal B →
      ∃ g : Gallery K.toSimplicialComplex,
        g.Connects A B ∧ g.length = galleryDist K.toSimplicialComplex A B := by
    intro A B hA hB
    by_cases hab : A = B
    · subst hab
      exact ⟨⟨[A], by simp, fun E hE => by simp at hE; subst hE; exact hA,
              List.IsChain.singleton A⟩,
             ⟨by simp, by simp⟩,
             by simp [Gallery.length, galleryDist_self]⟩
    · obtain ⟨g₀, hconn₀⟩ := K.gallery_connected A B hA hB
      have hne : {n | ∃ g : Gallery K.toSimplicialComplex,
          g.Connects A B ∧ g.length = n}.Nonempty :=
        ⟨g₀.length, g₀, ⟨hconn₀.1, hconn₀.2⟩, rfl⟩
      obtain ⟨g, hconn, hlen⟩ := Nat.sInf_mem hne
      exact ⟨g, hconn, by unfold galleryDist; rw [if_neg hab]; exact hlen⟩

  obtain ⟨g₁, hconn₁, hmin₁⟩ := min_gallery C C' hC hC'
  obtain ⟨g₂, hconn₂, hmin₂⟩ := min_gallery C' D hC' hD

  obtain ⟨g₃, hconn₃, hlen₃, hC'_mem⟩ :=
    Gallery.gallery_concat C C' D g₁ g₂ hconn₁ hconn₂

  have hmin₃ : g₃.length = galleryDist K.toSimplicialComplex C D := by
    rw [hlen₃, hmin₁, hmin₂, ← hdist]
  exact ⟨g₃, hconn₃, hmin₃, hC'_mem⟩

/-- Bundle of hypotheses needed for the opposite-chamber theorem in the
generic apartment-system setting: reversibility, distance equality, fold
decreases distance, maximality preservation, additivity, and existence of
galleries through chambers. -/
structure OppositeChamberHypGen {V : Type*} [DecidableEq V]
    (K : ChamberComplex V) (𝒜 : ApartmentSystem K) where
  apt_reversible_foldings :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∃ (f' : ChamberComplex.Folding cc),
            (∀ D : Finset V, cc.toSimplicialComplex.IsMaximal D →
              (D.image f.morph.toFun = D ↔ D.image f'.morph.toFun ≠ D)) ∧
            (∀ D : Finset V, cc.toSimplicialComplex.IsMaximal D →
              D.image f.morph.toFun = D →
              (D.image f'.morph.toFun).image f.morph.toFun = D)
  apt_dist_eq :
    ∀ A ∈ 𝒜.apartments,
      ∀ C D : Finset V,
        C ∈ A.faces → D ∈ A.faces →
        A.IsMaximal C → A.IsMaximal D →
        galleryDist A C D = galleryDist K.toSimplicialComplex C D
  fold_decreases_dist :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ C D : Finset V,
            cc.toSimplicialComplex.IsMaximal C →
            cc.toSimplicialComplex.IsMaximal D →
            C.image f.morph.toFun = C →
            D.image f.morph.toFun ≠ D →
            galleryDist cc.toSimplicialComplex C (D.image f.morph.toFun) <
              galleryDist cc.toSimplicialComplex C D
  fold_preserves_maximal :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ D : Finset V,
            cc.toSimplicialComplex.IsMaximal D →
            cc.toSimplicialComplex.IsMaximal (D.image f.morph.toFun)
  wall_sep_additive_dist :
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ C D C' : Finset V,
          cc.toSimplicialComplex.IsMaximal C →
          cc.toSimplicialComplex.IsMaximal D →
          cc.toSimplicialComplex.IsMaximal C' →
          (∀ (f : ChamberComplex.Folding cc),
            ChamberComplex.OppositeSides f C D) →
          galleryDist cc.toSimplicialComplex C D =
            galleryDist cc.toSimplicialComplex C C' +
            galleryDist cc.toSimplicialComplex C' D
  gallery_through_chamber :
    ∀ C C' D : Finset V,
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      K.toSimplicialComplex.IsMaximal D →
      galleryDist K.toSimplicialComplex C D =
        galleryDist K.toSimplicialComplex C C' +
        galleryDist K.toSimplicialComplex C' D →
      ∃ (g : Gallery K.toSimplicialComplex),
        g.Connects C D ∧
        g.length = galleryDist K.toSimplicialComplex C D ∧
        C' ∈ g.chambers

open scoped Classical in
/-- Wall-separation property for opposite chambers in a spherical apartment:
every folding separates them. -/
theorem wall_separates_opposite_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} {𝒜 : ApartmentSystem K}
    (hyp : OppositeChamberHypGen K 𝒜)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C D : Finset V) (hC : C ∈ A.faces) (hD : D ∈ A.faces)
    (hCmax : A.IsMaximal C) (hDmax : A.IsMaximal D)
    (hopp : AreOpposite K.toSimplicialComplex C D)
    (cc : ChamberComplex V) (hcc : cc.toSimplicialComplex = A)
    (f : ChamberComplex.Folding cc) :
    ChamberComplex.OppositeSides f C D := by
  by_contra h_not_opp
  have hCfm : C.image f.morph.toFun = C ∨ C.image f.morph.toFun ≠ C := em _
  have hDfm : D.image f.morph.toFun = D ∨ D.image f.morph.toFun ≠ D := em _
  have h_neg : ¬(C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∧
               ¬(D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C) := by
    constructor <;> intro h <;> exact h_not_opp (by unfold ChamberComplex.OppositeSides; tauto)
  obtain ⟨f', hcompl, hrev⟩ := hyp.apt_reversible_foldings A hA cc hcc f
  have hCmax_cc : cc.toSimplicialComplex.IsMaximal C := hcc ▸ hCmax
  have hDmax_cc : cc.toSimplicialComplex.IsMaximal D := hcc ▸ hDmax
  rcases hCfm with hfC | hfC <;> rcases hDfm with hfD | hfD
  ·
    have hf'D_moved : D.image f'.morph.toFun ≠ D := (hcompl D hDmax_cc).mp hfD
    have hff'D : (D.image f'.morph.toFun).image f.morph.toFun = D :=
      hrev D hDmax_cc hfD
    have hf'D_max := hyp.fold_preserves_maximal A hA cc hcc f' D hDmax_cc
    have hf_moves_f'D : (D.image f'.morph.toFun).image f.morph.toFun ≠
        D.image f'.morph.toFun := by rw [hff'D]; exact hf'D_moved.symm
    have hdist_lt := hyp.fold_decreases_dist A hA cc hcc f
      C (D.image f'.morph.toFun) hCmax_cc hf'D_max hfC hf_moves_f'D
    rw [hff'D] at hdist_lt
    have hf'D_in_A : D.image f'.morph.toFun ∈ A.faces := hcc ▸ hf'D_max.1
    have hdist_CD := hyp.apt_dist_eq A hA C D hC hD hCmax hDmax
    have hdist_Cf'D := hyp.apt_dist_eq A hA C (D.image f'.morph.toFun)
      hC hf'D_in_A hCmax (hcc ▸ hf'D_max)
    have heq_CD : galleryDist cc.toSimplicialComplex C D = galleryDist A C D :=
      congr_arg (fun s => galleryDist s C D) hcc
    have heq_Cf'D : galleryDist cc.toSimplicialComplex C (D.image f'.morph.toFun) =
        galleryDist A C (D.image f'.morph.toFun) :=
      congr_arg (fun s => galleryDist s C (D.image f'.morph.toFun)) hcc
    rw [heq_CD, heq_Cf'D] at hdist_lt
    rw [hdist_CD, hdist_Cf'D] at hdist_lt
    set f'D := D.image f'.morph.toFun with hf'D_def
    have hf'D_max_A : A.IsMaximal f'D := by
      have h : cc.toSimplicialComplex.IsMaximal f'D := hf'D_max
      rwa [hcc] at h
    have hf'D_bmax := 𝒜.maximal_in_apt_is_maximal A hA _ hf'D_max_A
    have hle := hopp.2.2 C (D.image f'.morph.toFun) hopp.1 hf'D_bmax
    exact Nat.not_lt.mpr hle hdist_lt
  · exact absurd (Or.inl ⟨hfC, hfD⟩ : ChamberComplex.OppositeSides f C D) h_not_opp
  · exact absurd (Or.inr ⟨hfD, hfC⟩ : ChamberComplex.OppositeSides f C D) h_not_opp
  ·
    have hf'C : C.image f'.morph.toFun = C := by
      by_contra h; exact hfC ((hcompl C hCmax_cc).mpr h)
    have hf'D : D.image f'.morph.toFun = D := by
      by_contra h; exact hfD ((hcompl D hDmax_cc).mpr h)
    obtain ⟨f'', hcompl', hrev'⟩ := hyp.apt_reversible_foldings A hA cc hcc f'
    have hf''C_moved : C.image f''.morph.toFun ≠ C := (hcompl' C hCmax_cc).mp hf'C
    have hf'f''C : (C.image f''.morph.toFun).image f'.morph.toFun = C :=
      hrev' C hCmax_cc hf'C
    have hf''C_max := hyp.fold_preserves_maximal A hA cc hcc f'' C hCmax_cc
    have hf'_moves : (C.image f''.morph.toFun).image f'.morph.toFun ≠
        C.image f''.morph.toFun := by rw [hf'f''C]; exact hf''C_moved.symm
    have hdist_lt := hyp.fold_decreases_dist A hA cc hcc f'
      D (C.image f''.morph.toFun) hDmax_cc hf''C_max hf'D hf'_moves
    rw [hf'f''C] at hdist_lt
    have hf''C_in_A : C.image f''.morph.toFun ∈ A.faces := hcc ▸ hf''C_max.1
    have hdist_DC := hyp.apt_dist_eq A hA D C hD hC hDmax hCmax
    have hdist_Df''C := hyp.apt_dist_eq A hA D (C.image f''.morph.toFun)
      hD hf''C_in_A hDmax (hcc ▸ hf''C_max)
    have heq_DC : galleryDist cc.toSimplicialComplex D C = galleryDist A D C :=
      congr_arg (fun s => galleryDist s D C) hcc
    have heq_Df''C : galleryDist cc.toSimplicialComplex D (C.image f''.morph.toFun) =
        galleryDist A D (C.image f''.morph.toFun) :=
      congr_arg (fun s => galleryDist s D (C.image f''.morph.toFun)) hcc
    rw [heq_DC, heq_Df''C] at hdist_lt
    rw [hdist_DC, hdist_Df''C] at hdist_lt
    set f''C := C.image f''.morph.toFun with hf''C_def
    have hf''C_max_A : A.IsMaximal f''C := by
      have h : cc.toSimplicialComplex.IsMaximal f''C := hf''C_max
      rwa [hcc] at h
    have hf''C_bmax := 𝒜.maximal_in_apt_is_maximal A hA _ hf''C_max_A
    have hopp' := areOpposite_symm hopp
    have hle := hopp'.2.2 D (C.image f''.morph.toFun) hopp'.1 hf''C_bmax
    exact Nat.not_lt.mpr hle hdist_lt

open scoped Classical in
/-- Every chamber $C'$ of an apartment lies on some minimal gallery
between an opposite pair $C, D$. -/
theorem chamber_in_minimal_gallery_of_opposite_gen
    {V : Type*} [DecidableEq V]
    {K : ChamberComplex V} {𝒜 : ApartmentSystem K}
    (hyp : OppositeChamberHypGen K 𝒜)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C D : Finset V) (hC : C ∈ A.faces) (hD : D ∈ A.faces)
    (hCmax : A.IsMaximal C) (hDmax : A.IsMaximal D)
    (hopp : AreOpposite K.toSimplicialComplex C D)
    (cc : ChamberComplex V) (hcc : cc.toSimplicialComplex = A)
    (C' : Finset V) (hC' : C' ∈ A.faces) (hC'max : A.IsMaximal C') :
    ∃ (g : Gallery K.toSimplicialComplex),
      g.Connects C D ∧
      g.length = galleryDist K.toSimplicialComplex C D ∧
      C' ∈ g.chambers := by
  have h_all_sep : ∀ (f : ChamberComplex.Folding cc),
      ChamberComplex.OppositeSides f C D :=
    fun f => wall_separates_opposite_gen hyp A hA C D hC hD hCmax hDmax hopp cc hcc f
  have h_add := hyp.wall_sep_additive_dist A hA cc hcc C D C'
    (hcc ▸ hCmax) (hcc ▸ hDmax) (hcc ▸ hC'max) h_all_sep
  have hdCD := hyp.apt_dist_eq A hA C D hC hD hCmax hDmax
  have hdCC' := hyp.apt_dist_eq A hA C C' hC hC' hCmax hC'max
  have hdC'D := hyp.apt_dist_eq A hA C' D hC' hD hC'max hDmax
  rw [← hcc] at hdCD hdCC' hdC'D
  rw [hdCD, hdCC', hdC'D] at h_add
  have hCbmax := 𝒜.maximal_in_apt_is_maximal A hA C hCmax
  have hC'bmax := 𝒜.maximal_in_apt_is_maximal A hA C' hC'max
  have hDbmax := 𝒜.maximal_in_apt_is_maximal A hA D hDmax
  exact hyp.gallery_through_chamber C C' D hCbmax hC'bmax hDbmax h_add


/-- A face bijection between simplicial complexes preserves maximality. -/
lemma face_bij_maps_maximal
    {V : Type*} [DecidableEq V]
    (B A : SimplicialComplex V)
    (ψ : V → V) (hψ_bij : Function.Bijective ψ)
    (hψ_faces : ∀ s, s ∈ B.faces ↔ s.image ψ ∈ A.faces)
    (s : Finset V) (hs : B.IsMaximal s) : A.IsMaximal (s.image ψ) := by
  constructor
  · exact (hψ_faces s).mp hs.1
  · intro t ht hst
    let ψ_inv := Function.surjInv hψ_bij.2
    have hψ_inv_right : ψ ∘ ψ_inv = id := Function.comp_surjInv hψ_bij.2
    have hψ_inv_left : ψ_inv ∘ ψ = id := by
      funext x; simp [Function.comp]; exact hψ_bij.1 (Function.surjInv_eq hψ_bij.2 (ψ x))

    have ht_eq : t = (t.image ψ_inv).image ψ := by
      rw [Finset.image_image, hψ_inv_right, Finset.image_id]
    have ht_inv_face : t.image ψ_inv ∈ B.faces := by
      rw [ht_eq] at ht; exact (hψ_faces _).mpr ht
    have hs_sub : s ⊆ t.image ψ_inv := by
      intro v hv
      have hv' : ψ v ∈ t := hst (Finset.mem_image_of_mem ψ hv)
      rw [Finset.mem_image]
      exact ⟨ψ v, hv', congr_fun hψ_inv_left v⟩
    have heq := hs.2 _ ht_inv_face hs_sub
    rw [heq, ← ht_eq]

/-- A face bijection between simplicial complexes preserves adjacency. -/
lemma face_bij_maps_adjacent
    {V : Type*} [DecidableEq V]
    (B A : SimplicialComplex V)
    (ψ : V → V) (hψ_bij : Function.Bijective ψ)
    (hψ_faces : ∀ s, s ∈ B.faces ↔ s.image ψ ∈ A.faces)
    (E F : Finset V) (hEF : B.Adjacent E F) :
    A.Adjacent (E.image ψ) (F.image ψ) := by
  obtain ⟨hE_max, hF_max, hne, G, hGE, hGF⟩ := hEF
  refine ⟨face_bij_maps_maximal B A ψ hψ_bij hψ_faces E hE_max,
          face_bij_maps_maximal B A ψ hψ_bij hψ_faces F hF_max,
          fun h => hne (Finset.image_injective hψ_bij.1 h),
          G.image ψ, ?_, ?_⟩
  · constructor
    · exact ⟨(hψ_faces G).mp hGE.1.1, (hψ_faces E).mp hGE.1.2.1,
            Finset.image_subset_image hGE.1.2.2⟩
    · rw [← Finset.image_sdiff E G hψ_bij.1, Finset.card_image_of_injective _ hψ_bij.1]
      exact hGE.2

  · constructor
    · exact ⟨(hψ_faces G).mp hGF.1.1, (hψ_faces F).mp hGF.1.2.1,
            Finset.image_subset_image hGF.1.2.2⟩
    · rw [← Finset.image_sdiff F G hψ_bij.1, Finset.card_image_of_injective _ hψ_bij.1]
      exact hGF.2

/-- Apply a relation-respecting map to a chain to obtain a chain in the
target. -/
lemma isChain_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} {f : α → β}
    (h : ∀ a b, R a b → S (f a) (f b)) {l : List α} (hl : List.IsChain R l) :
    List.IsChain S (l.map f) := by
  induction hl with
  | nil => exact .nil
  | singleton a => exact .singleton (f a)
  | cons_cons hab hbc ih => exact .cons_cons (h _ _ hab) ih

/-- A face bijection between two apartments yields the inequality
$d_{A'}(f(C), f(D)) \le d_A(C, D)$ between gallery distances. -/
lemma face_bij_gallery_le
    {V : Type*} [DecidableEq V]
    (B A : SimplicialComplex V)
    (ψ : V → V) (hψ_bij : Function.Bijective ψ)
    (hψ_faces : ∀ s, s ∈ B.faces ↔ s.image ψ ∈ A.faces)
    (C D : Finset V) :
    galleryDist A (C.image ψ) (D.image ψ) ≤ galleryDist B C D := by
  by_cases hCD : C = D
  · subst hCD; simp [galleryDist]
  · have hCD' : C.image ψ ≠ D.image ψ := fun h => hCD (Finset.image_injective hψ_bij.1 h)
    simp only [galleryDist, hCD, hCD', ite_false]


    by_cases hne : {n | ∃ g : Gallery B, Gallery.Connects g C D ∧ g.length = n}.Nonempty
    · obtain ⟨g, hconn, hlen⟩ := Nat.sInf_mem hne

      have hmap_max : ∀ E ∈ g.chambers.map (Finset.image ψ), A.IsMaximal E := by
        intro E hE; rw [List.mem_map] at hE; obtain ⟨F, hFmem, rfl⟩ := hE
        exact face_bij_maps_maximal B A ψ hψ_bij hψ_faces F (g.all_maximal F hFmem)
      have hmap_chain : List.IsChain A.Adjacent (g.chambers.map (Finset.image ψ)) :=
        isChain_map (face_bij_maps_adjacent B A ψ hψ_bij hψ_faces) g.adjacent_consecutive
      have hmap_len : (g.chambers.map (Finset.image ψ)).length > 0 := by
        simp [List.length_map]; exact g.length_pos
      let g' : Gallery A := ⟨g.chambers.map (Finset.image ψ), hmap_len, hmap_max, hmap_chain⟩
      have hconn' : g'.Connects (C.image ψ) (D.image ψ) :=
        ⟨by simp [g', List.head?_map, hconn.1], by simp [g', List.getLast?_map, hconn.2]⟩
      have hlen' : g'.length = g.length := by
        simp [g', Gallery.length, List.length_map]
      have hmem : g.length ∈ {n | ∃ g : Gallery A, Gallery.Connects g (C.image ψ) (D.image ψ) ∧ g.length = n} :=
        ⟨g', hconn', hlen'⟩
      rw [← hlen]
      exact Nat.sInf_le hmem
    ·
      rw [Set.not_nonempty_iff_eq_empty] at hne

      let ψ_inv := Function.surjInv hψ_bij.2
      have hψ_inv_right : ψ ∘ ψ_inv = id := Function.comp_surjInv hψ_bij.2
      have hψ_inv_left : ψ_inv ∘ ψ = id := by
        funext x; simp [Function.comp]; exact hψ_bij.1 (Function.surjInv_eq hψ_bij.2 (ψ x))
      have hψ_inv_bij : Function.Bijective ψ_inv := by
        constructor
        · intro a b hab
          have := congr_arg ψ hab
          simp at this

          rwa [Function.surjInv_eq hψ_bij.2, Function.surjInv_eq hψ_bij.2] at this
        · intro b
          exact ⟨ψ b, congr_fun hψ_inv_left b⟩

      have hne_A : {n | ∃ g : Gallery A, g.Connects (C.image ψ) (D.image ψ) ∧ g.length = n} = ∅ := by
        ext n; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ⟨g_A, hconn_A, hlen_A⟩

        have hmap_max : ∀ E ∈ g_A.chambers.map (Finset.image ψ_inv), B.IsMaximal E := by
          intro E hE; rw [List.mem_map] at hE; obtain ⟨F, hFmem, rfl⟩ := hE
          have hF_A_max := g_A.all_maximal F hFmem
          exact face_bij_maps_maximal A B ψ_inv hψ_inv_bij
            (fun s => by
              constructor
              · intro hs
                have : s = (s.image ψ_inv).image ψ := by
                  rw [Finset.image_image, hψ_inv_right, Finset.image_id]
                rw [this] at hs; exact (hψ_faces _).mpr hs
              · intro hs
                have h1 := (hψ_faces _).mp hs
                convert h1 using 1; rw [Finset.image_image, hψ_inv_right, Finset.image_id])
            F hF_A_max
        have hmap_chain : List.IsChain B.Adjacent (g_A.chambers.map (Finset.image ψ_inv)) :=
          isChain_map (face_bij_maps_adjacent A B ψ_inv hψ_inv_bij
            (fun s => by
              constructor
              · intro hs
                have : s = (s.image ψ_inv).image ψ := by
                  rw [Finset.image_image, hψ_inv_right, Finset.image_id]
                rw [this] at hs; exact (hψ_faces _).mpr hs
              · intro hs
                have h1 := (hψ_faces _).mp hs
                convert h1 using 1; rw [Finset.image_image, hψ_inv_right, Finset.image_id]))
            g_A.adjacent_consecutive
        have hmap_len : (g_A.chambers.map (Finset.image ψ_inv)).length > 0 := by
          simp [List.length_map]; exact g_A.length_pos
        let g_B : Gallery B := ⟨g_A.chambers.map (Finset.image ψ_inv), hmap_len, hmap_max, hmap_chain⟩
        have hψ_inv_C : (C.image ψ).image ψ_inv = C := by
          rw [Finset.image_image, hψ_inv_left, Finset.image_id]
        have hψ_inv_D : (D.image ψ).image ψ_inv = D := by
          rw [Finset.image_image, hψ_inv_left, Finset.image_id]
        have hconn_B : g_B.Connects C D :=
          ⟨by simp [g_B, List.head?_map]
              exact ⟨C.image ψ, hconn_A.1, hψ_inv_C⟩,
           by simp [g_B, List.getLast?_map]
              exact ⟨D.image ψ, hconn_A.2, hψ_inv_D⟩⟩

        have : n ∈ {n | ∃ g : Gallery B, g.Connects C D ∧ g.length = n} := by
          simp only [Set.mem_setOf_eq]
          refine ⟨g_B, hconn_B, ?_⟩
          simp [g_B, Gallery.length, List.length_map]
          exact hlen_A
        rw [hne] at this; exact this
      rw [hne, hne_A]

/-- A spherical apartment has an opposite chamber pair: there exist
chambers $C, D$ at maximal gallery distance. -/
theorem spherical_apt_has_opposite_pair
    {V : Type*} [DecidableEq V]
    (K : ChamberComplex V) (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (hfin : Set.Finite A.faces) :
    ∃ C D, A.IsMaximal C ∧ A.IsMaximal D ∧
      AreOpposite K.toSimplicialComplex C D := by

  have chambers_finite : Set.Finite {C | A.IsMaximal C} :=
    hfin.subset (fun C hC => hC.1)
  let ch_fs := chambers_finite.toFinset

  obtain ⟨s, hs⟩ := 𝒜.apt_nonempty A hA
  obtain ⟨_, _, cc_A, hcc_A, _⟩ := 𝒜.apt_is_coxeter A hA
  have hs_cc : s ∈ cc_A.toSimplicialComplex.faces := hcc_A ▸ hs
  obtain ⟨C₁, hC₁_max_cc, _⟩ := cc_A.exists_maximal s hs_cc
  have hC₁_A_max : A.IsMaximal C₁ := hcc_A ▸ hC₁_max_cc
  have hne : ch_fs.Nonempty :=
    ⟨C₁, chambers_finite.mem_toFinset.mpr hC₁_A_max⟩

  let pairs := ch_fs ×ˢ ch_fs
  obtain ⟨⟨C₀, D₀⟩, hmem, hmax⟩ :=
    pairs.exists_max_image (fun p => galleryDist K.toSimplicialComplex p.1 p.2)
      (Finset.Nonempty.product hne hne)
  have hC₀_max : A.IsMaximal C₀ :=
    chambers_finite.mem_toFinset.mp (Finset.mem_product.mp hmem).1
  have hD₀_max : A.IsMaximal D₀ :=
    chambers_finite.mem_toFinset.mp (Finset.mem_product.mp hmem).2
  have hC₀_K := 𝒜.maximal_in_apt_is_maximal A hA C₀ hC₀_max
  have hD₀_K := 𝒜.maximal_in_apt_is_maximal A hA D₀ hD₀_max

  refine ⟨C₀, D₀, hC₀_max, hD₀_max, hC₀_K, hD₀_K, fun C' D' hC'_K hD'_K => ?_⟩


  obtain ⟨B, hB, hC'_B, hD'_B⟩ := 𝒜.contains_pair C' D' hC'_K hD'_K
  have hC'_Bmax := 𝒜.building_maximal_in_apt_is_apt_maximal B hB C' hC'_B hC'_K
  have hD'_Bmax := 𝒜.building_maximal_in_apt_is_apt_maximal B hB D' hD'_B hD'_K

  have hB_dist : galleryDist B C' D' = galleryDist K.toSimplicialComplex C' D' :=
    𝒜.apt_dist_eq_gen B hB C' D' hC'_B hD'_B hC'_Bmax hD'_Bmax
  have hA_dist : galleryDist A C₀ D₀ = galleryDist K.toSimplicialComplex C₀ D₀ :=
    𝒜.apt_dist_eq_gen A hA C₀ D₀ hC₀_max.1 hD₀_max.1 hC₀_max hD₀_max


  have hC₁_K := 𝒜.maximal_in_apt_is_maximal A hA C₁ hC₁_A_max
  obtain ⟨B', hB', hC₁_B', hC'_B'⟩ := 𝒜.contains_pair C₁ C' hC₁_K hC'_K
  have hC'_B'max := 𝒜.building_maximal_in_apt_is_apt_maximal B' hB' C' hC'_B' hC'_K

  obtain ⟨ψ₁, hψ₁_bij, hψ₁_faces⟩ :=
    𝒜.iso_bijective B hB B' hB' C' hC'_B hC'_B' hC'_Bmax

  have hC₁_B'max := 𝒜.building_maximal_in_apt_is_apt_maximal B' hB' C₁ hC₁_B' hC₁_K
  obtain ⟨ψ₂, hψ₂_bij, hψ₂_faces⟩ :=
    𝒜.iso_bijective B' hB' A hA C₁ hC₁_B' hC₁_A_max.1 hC₁_B'max

  let ψ := ψ₂ ∘ ψ₁
  have hψ_bij : Function.Bijective ψ := Function.Bijective.comp hψ₂_bij hψ₁_bij
  have hψ_faces : ∀ s, s ∈ B.faces ↔ s.image ψ ∈ A.faces := by
    intro s
    constructor
    · intro hs
      have h1 := (hψ₁_faces s).mp hs
      have h2 := (hψ₂_faces (s.image ψ₁)).mp h1
      convert h2 using 1
      simp [ψ, Finset.image_image]
    · intro hs
      have : s.image ψ = (s.image ψ₁).image ψ₂ := by simp [ψ, Finset.image_image]
      rw [this] at hs
      have h2 := (hψ₂_faces (s.image ψ₁)).mpr hs
      exact (hψ₁_faces s).mpr h2

  have hψC'_max : A.IsMaximal (C'.image ψ) :=
    face_bij_maps_maximal B A ψ hψ_bij hψ_faces C' hC'_Bmax
  have hψD'_max : A.IsMaximal (D'.image ψ) :=
    face_bij_maps_maximal B A ψ hψ_bij hψ_faces D' hD'_Bmax

  let ψ_inv := Function.surjInv hψ_bij.2
  have hψ_inv_right : ψ ∘ ψ_inv = id := Function.comp_surjInv hψ_bij.2
  have hψ_inv_left : ψ_inv ∘ ψ = id := by
    funext x; simp [Function.comp]; exact hψ_bij.1 (Function.surjInv_eq hψ_bij.2 (ψ x))
  have hψ_inv_bij : Function.Bijective ψ_inv := by
    constructor
    · intro a b hab
      have := congr_arg ψ hab
      simp at this

      rwa [Function.surjInv_eq hψ_bij.2, Function.surjInv_eq hψ_bij.2] at this
    · intro b
      exact ⟨ψ b, congr_fun hψ_inv_left b⟩
  have hψ_inv_faces : ∀ s, s ∈ A.faces ↔ s.image ψ_inv ∈ B.faces := by
    intro s
    constructor
    · intro hs
      have : s = (s.image ψ_inv).image ψ := by
        rw [Finset.image_image, hψ_inv_right, Finset.image_id]
      rw [this] at hs
      exact (hψ_faces _).mpr hs
    · intro hs
      have h1 := (hψ_faces _).mp hs
      convert h1 using 1
      rw [Finset.image_image, hψ_inv_right, Finset.image_id]

  have hgd_le : galleryDist A (C'.image ψ) (D'.image ψ) ≤ galleryDist B C' D' :=
    face_bij_gallery_le B A ψ hψ_bij hψ_faces C' D'
  have hgd_ge_raw : galleryDist B ((C'.image ψ).image ψ_inv) ((D'.image ψ).image ψ_inv) ≤
      galleryDist A (C'.image ψ) (D'.image ψ) :=
    face_bij_gallery_le A B ψ_inv hψ_inv_bij hψ_inv_faces (C'.image ψ) (D'.image ψ)
  have hC'_eq : (C'.image ψ).image ψ_inv = C' := by
    rw [Finset.image_image, hψ_inv_left, Finset.image_id]
  have hD'_eq : (D'.image ψ).image ψ_inv = D' := by
    rw [Finset.image_image, hψ_inv_left, Finset.image_id]
  rw [hC'_eq, hD'_eq] at hgd_ge_raw

  have hgd_eq : galleryDist B C' D' = galleryDist A (C'.image ψ) (D'.image ψ) :=
    le_antisymm hgd_ge_raw hgd_le

  have hψC'_K := 𝒜.maximal_in_apt_is_maximal A hA (C'.image ψ) hψC'_max
  have hψD'_K := 𝒜.maximal_in_apt_is_maximal A hA (D'.image ψ) hψD'_max
  have hA_ψdist : galleryDist A (C'.image ψ) (D'.image ψ) =
      galleryDist K.toSimplicialComplex (C'.image ψ) (D'.image ψ) :=
    𝒜.apt_dist_eq_gen A hA _ _ hψC'_max.1 hψD'_max.1 hψC'_max hψD'_max
  have hψ_in_ch : (C'.image ψ, D'.image ψ) ∈ pairs := by
    simp only [pairs, Finset.mem_product]
    exact ⟨chambers_finite.mem_toFinset.mpr hψC'_max,
           chambers_finite.mem_toFinset.mpr hψD'_max⟩
  have hmax_bound : galleryDist K.toSimplicialComplex (C'.image ψ) (D'.image ψ) ≤
      galleryDist K.toSimplicialComplex C₀ D₀ :=
    hmax _ hψ_in_ch


  omega

/-- Two apartments with the same set of chambers are equal. -/
theorem apartments_eq_of_same_chambers
    {V : Type*} [DecidableEq V]
    (K : ChamberComplex V)
    (𝒜₁ 𝒜₂ : ApartmentSystem K)
    (A : SimplicialComplex V) (hA₁ : A ∈ 𝒜₁.apartments)
    (B : SimplicialComplex V) (hB₂ : B ∈ 𝒜₂.apartments)
    (hchambers : ∀ E, A.IsMaximal E ↔ B.IsMaximal E) :
    A = B := by

  obtain ⟨_, _, ccA, hccA, _⟩ := 𝒜₁.apt_is_coxeter A hA₁
  obtain ⟨_, _, ccB, hccB, _⟩ := 𝒜₂.apt_is_coxeter B hB₂

  have h_faces_eq : A.faces = B.faces := by
    ext σ
    constructor
    ·
      intro hσA

      have hσ_cc : σ ∈ ccA.toSimplicialComplex.faces := hccA ▸ hσA
      obtain ⟨C, hC_max_cc, hσ_sub_C⟩ := ccA.exists_maximal σ hσ_cc

      have hC_max_A : A.IsMaximal C := hccA ▸ hC_max_cc

      have hC_max_B : B.IsMaximal C := (hchambers C).mp hC_max_A

      exact B.down_closed hC_max_B.1 hσ_sub_C (A.nonempty_of_mem σ hσA)
    ·
      intro hσB
      have hσ_cc : σ ∈ ccB.toSimplicialComplex.faces := hccB ▸ hσB
      obtain ⟨C, hC_max_cc, hσ_sub_C⟩ := ccB.exists_maximal σ hσ_cc
      have hC_max_B : B.IsMaximal C := hccB ▸ hC_max_cc
      have hC_max_A : A.IsMaximal C := (hchambers C).mpr hC_max_B
      exact A.down_closed hC_max_A.1 hσ_sub_C (B.nonempty_of_mem σ hσB)

  cases A with | mk faces_A nonempty_A down_closed_A =>
  cases B with | mk faces_B nonempty_B down_closed_B =>
  simp only [SimplicialComplex.mk.injEq]
  exact h_faces_eq

/-- Adjacency in $A$ follows from adjacency in $K \supseteq A$ when both
chambers are maximal in $A$. -/
theorem adjacent_in_subcomplex
    {A K : SimplicialComplex V} (_hsub : IsSubcomplex A K)
    {C D : Finset V} (hadj : K.Adjacent C D)
    (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    A.Adjacent C D := by
  obtain ⟨_, _, hne, F, hFC, hFD⟩ := hadj
  have hF_ne : F.Nonempty := K.nonempty_of_mem _ hFC.1.1
  have hF_A : F ∈ A.faces := A.down_closed hC.1 hFC.1.2.2 hF_ne
  exact ⟨hC, hD, hne, F, ⟨⟨hF_A, hC.1, hFC.1.2.2⟩, hFC.2⟩, ⟨⟨hF_A, hD.1, hFD.1.2.2⟩, hFD.2⟩⟩

/-- A chain in $K$ remains a chain in $A \subseteq K$ when all entries are
maximal in $A$. -/
theorem chain_transfer_to_subcomplex
    {A K : SimplicialComplex V} (hsub : IsSubcomplex A K)
    (l : List (Finset V))
    (hchain : List.IsChain K.Adjacent l)
    (hmax : ∀ E ∈ l, A.IsMaximal E) :
    List.IsChain A.Adjacent l := by
  induction hchain with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.IsChain.singleton a
  | cons_cons hab htail ih =>
    apply List.IsChain.cons_cons
    · exact adjacent_in_subcomplex hsub hab
        (hmax _ List.mem_cons_self)
        (hmax _ (List.mem_cons.mpr (Or.inr List.mem_cons_self)))
    · exact ih (fun E hE => hmax E (List.mem_cons.mpr (Or.inr hE)))

/-- The gallery distance computed in an apartment is at most the gallery
distance computed in the ambient building. -/
theorem galleryDist_apt_le_building
    (K : ChamberComplex V) (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    galleryDist A C D ≤ galleryDist K.toSimplicialComplex C D := by
  by_cases hCD : C = D
  · subst hCD; simp [galleryDist]
  · have hC_K := 𝒜.maximal_in_apt_is_maximal A hA C hC
    have hD_K := 𝒜.maximal_in_apt_is_maximal A hA D hD
    obtain ⟨gK, hgK_conn⟩ := K.gallery_connected C D hC_K hD_K
    have hne_K : {n | ∃ g : Gallery K.toSimplicialComplex, g.Connects C D ∧ g.length = n}.Nonempty :=
      ⟨gK.length, gK, ⟨hgK_conn.1, hgK_conn.2⟩, rfl⟩
    have hgd_K : galleryDist K.toSimplicialComplex C D =
        sInf {n | ∃ g : Gallery K.toSimplicialComplex, g.Connects C D ∧ g.length = n} := by
      unfold galleryDist; simp [hCD]
    have hmem := Nat.sInf_mem hne_K
    obtain ⟨g₀, hg₀_conn, hg₀_len⟩ := hmem
    have hg₀_min : g₀.length = galleryDist K.toSimplicialComplex C D := by
      rw [hgd_K, hg₀_len]
    have hg₀_in_A : ∀ E ∈ g₀.chambers, E ∈ A.faces :=
      𝒜.gallery_convex A hA C D hC.1 hC_K hD.1 hD_K g₀ hg₀_conn hg₀_min
    have hg₀_A_max : ∀ E ∈ g₀.chambers, A.IsMaximal E := fun E hE =>
      𝒜.building_maximal_in_apt_is_apt_maximal A hA E (hg₀_in_A E hE) (g₀.all_maximal E hE)
    have hsub := 𝒜.sub A hA
    have hg₀_A_chain : List.IsChain A.Adjacent g₀.chambers :=
      chain_transfer_to_subcomplex hsub g₀.chambers g₀.adjacent_consecutive hg₀_A_max
    let gA : Gallery A := ⟨g₀.chambers, g₀.length_pos, hg₀_A_max, hg₀_A_chain⟩
    calc galleryDist A C D
        ≤ gA.length := by
          unfold galleryDist; simp [hCD]; exact Nat.sInf_le ⟨gA, hg₀_conn, rfl⟩
      _ = galleryDist K.toSimplicialComplex C D := hg₀_min

