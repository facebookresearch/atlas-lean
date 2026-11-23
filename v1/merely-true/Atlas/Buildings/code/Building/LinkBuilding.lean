/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.LinkBuildingIsoHelper
import Atlas.Buildings.code.Building.LinkCoxeterHelper
import Atlas.Buildings.code.Building.UniqueLabellingHelper
import Atlas.Buildings.code.Building.GalleryProjectionHelper

open scoped Classical


variable {V : Type} [DecidableEq V]

namespace SimplicialComplex

/-- When $\tau$ is disjoint from $\sigma$, the set difference $(\sigma \cup \tau) \setminus
(\sigma \cup F)$ equals $\tau \setminus F$. -/
theorem sdiff_union_eq_sdiff_of_disjoint' {σ F τ : Finset V}
    (_hF_disj : Disjoint σ F) (hτ_disj : Disjoint σ τ) :
    (σ ∪ τ) \ (σ ∪ F) = τ \ F := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact ⟨h1, fun hv => h2 (Or.inr hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h1, fun h => h.elim (fun h => Finset.disjoint_right.mp hτ_disj h1 h) h2⟩

/-- A maximal face $\tau$ of the link $\mathrm{lk}_K(\sigma)$ lifts to a maximal face $\sigma \cup
\tau$ of the ambient complex $K$. -/
theorem union_maximal_of_linkComplex_maximal' {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_max : (K.linkComplex σ hσ).IsMaximal τ) :
    K.IsMaximal (σ ∪ τ) := by
  have hτ_link := hτ_max.1
  rw [mem_linkComplex_iff] at hτ_link
  refine ⟨hτ_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hτ_sub : τ ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hτ_link.2.1 hv⟩
    rw [hτ_max.2 (w \ σ) hw_link hτ_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hτ_link.1
    exact Finset.disjoint_right.mp hτ_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))

/-- The converse direction: if $\sigma \cup \tau$ is maximal in $K$ and $\tau$ lies in the link of
$\sigma$, then $\tau$ is maximal in $\mathrm{lk}_K(\sigma)$. -/
theorem linkComplex_maximal_of_union_maximal' {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_link : τ ∈ (K.linkComplex σ hσ).faces)
    (hστ_max : K.IsMaximal (σ ∪ τ)) :
    (K.linkComplex σ hσ).IsMaximal τ := by
  have hτ_data := (mem_linkComplex_iff K σ hσ τ).mp hτ_link
  refine ⟨hτ_link, fun y hy hτy => ?_⟩
  have hy_data := (mem_linkComplex_iff K σ hσ y).mp hy
  have h_eq := hστ_max.2 (σ ∪ y) hy_data.2.2 (Finset.union_subset_union_right hτy)
  ext v
  constructor
  · intro hv
    have := h_eq ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hτ_data.2.1 hv)) id
  · intro hv
    have := h_eq.symm ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hy_data.2.1 hv)) id

/-- The link operation is monotone with respect to subcomplex inclusion: if $A$ is a subcomplex of
$K$, then $\mathrm{lk}_A(\sigma)$ is a subcomplex of $\mathrm{lk}_K(\sigma)$. -/
theorem linkComplex_sub {K A : SimplicialComplex V}
    (hA : IsSubcomplex A K) (σ : Finset V) (hσK : σ ∈ K.faces) (hσA : σ ∈ A.faces) :
    IsSubcomplex (A.linkComplex σ hσA) (K.linkComplex σ hσK) := by
  intro τ hτ
  rw [mem_linkComplex_iff] at hτ ⊢
  exact ⟨hτ.1, hτ.2.1, hA hτ.2.2⟩

end SimplicialComplex

/-- Every face of the link $\mathrm{lk}_K(\sigma)$ extends to a maximal face of the link, witnessed
by extending a chamber of $K$ containing $\sigma \cup s$ and removing $\sigma$. -/
theorem link_exists_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
    ∀ s ∈ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).faces,
      ∃ C, (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C ∧ s ⊆ C := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ
  intro s hs
  have hs_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ s).mp hs
  obtain ⟨C, hC_max, hσs_sub⟩ := b.toChamberComplex.exists_maximal (σ ∪ s) hs_data.2.2
  have hσ_sub_C : σ ⊆ C := Finset.subset_union_left.trans hσs_sub
  have hne : (C \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hs_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩⟩
  have hCσ_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ C hC_max.1 hσ_sub_C hne
  have hC_eq : σ ∪ (C \ σ) = C := Finset.union_sdiff_of_subset hσ_sub_C
  have hCσ_max_K : K.IsMaximal (σ ∪ (C \ σ)) := by rw [hC_eq]; exact hC_max
  have hCσ_max_lk : lk.IsMaximal (C \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hCσ_link hCσ_max_K
  have hs_sub : s ⊆ C \ σ := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩
  exact ⟨C \ σ, hCσ_max_lk, hs_sub⟩



/-- A maximal face of a link apartment is also maximal in the link of the whole building, by
lifting through the ambient apartment structure. -/
theorem link_maximal_in_apt_is_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ C, A.IsMaximal C →
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C := by
  intro L hL C hC_max_L
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  have hσC_max_A : A.IsMaximal (σ ∪ C) :=
    SimplicialComplex.union_maximal_of_linkComplex_maximal' hσA hC_max_L

  have hσC_max_K : K.IsMaximal (σ ∪ C) :=
    𝒜.maximal_in_apt_is_maximal A hA_apt (σ ∪ C) hσC_max_A

  have hC_link : C ∈ (K.linkComplex σ hσ).faces :=
    SimplicialComplex.linkComplex_sub (𝒜.sub A hA_apt) σ hσ hσA hC_max_L.1

  exact SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hC_link hσC_max_K



/-- A face that is globally maximal in the link and lies in a link apartment $A$ is also maximal
inside $A$ as a link apartment. -/
theorem link_building_maximal_in_apt_is_apt_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∀ C, C ∈ A.faces →
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C →
      A.IsMaximal C := by
  intro L hL C hC_L hC_max_lk
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem


  have hσC_max_K := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC_max_lk

  have hC_data := (SimplicialComplex.mem_linkComplex_iff A σ hσA C).mp hC_L
  have hσC_A : (σ ∪ C) ∈ A.faces := hC_data.2.2

  have hσC_max_A := 𝒜.building_maximal_in_apt_is_apt_maximal A hA_apt (σ ∪ C) hσC_A hσC_max_K

  exact SimplicialComplex.linkComplex_maximal_of_union_maximal' hσA hC_L hσC_max_A

/-- Every link apartment is nonempty: it contains $C \setminus \sigma$ for any chamber $C$ of the
ambient apartment that strictly contains $\sigma$. -/
theorem link_apt_nonempty
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA}) :
    ∀ A ∈ link_apts, ∃ s, s ∈ A.faces := by
  intro L hL
  rw [h_link_apts] at hL
  obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem

  obtain ⟨_, _, cc, hcc_eq, _⟩ := 𝒜.apt_is_coxeter A hA_apt
  have hσ_cc : σ ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hσA
  obtain ⟨C, hC_max_cc, hσ_sub_C⟩ := cc.exists_maximal σ hσ_cc
  have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max_cc
  have hC_max_K : K.IsMaximal C := 𝒜.maximal_in_apt_is_maximal A hA_apt C hC_max_A

  have hσ_ne_C : σ ≠ C := by
    intro h_eq
    obtain ⟨C₀, hC₀_max, hσ_sub⟩ := hσ_proper
    have hC_eq_C₀ : C = C₀ := hC_max_K.2 C₀ hC₀_max.1 (h_eq ▸ hσ_sub.1)
    rw [h_eq, hC_eq_C₀] at hσ_sub
    exact hσ_sub.ne rfl
  have hne : (C \ σ).Nonempty := by
    rcases Finset.exists_of_ssubset (Finset.lt_iff_ssubset.mpr (Finset.ssubset_iff_subset_ne.mpr ⟨hσ_sub_C, hσ_ne_C⟩)) with ⟨v, hv, hv'⟩
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hv'⟩⟩
  exact ⟨C \ σ, SimplicialComplex.mem_linkComplex_of_sdiff A σ hσA C hC_max_A.1 hσ_sub_C hne⟩





namespace Building

/-- Any two chambers $C', D'$ of the link both lie in a common link apartment, obtained from an
ambient apartment containing the lifted chambers $\sigma \cup C'$ and $\sigma \cup D'$. -/
theorem link_contains_pair (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (link_apts : Set (SimplicialComplex V))
    (h_link_apts : link_apts =
      {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
        L = A.linkComplex σ hσA})
    (C' D' : Finset V)
    (hC'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C')
    (hD'_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D') :
    ∃ A ∈ link_apts, C' ∈ A.faces ∧ D' ∈ A.faces := by
  set K := b.toChamberComplex.toSimplicialComplex
  set 𝒜 := b.apartmentSystem
  have hσC'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC'_max
  have hσD'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hD'_max
  obtain ⟨A, hA_apt, hC'_A, hD'_A⟩ := 𝒜.contains_pair
    (σ ∪ C') (σ ∪ D') hσC'_max hσD'_max
  have hσA : σ ∈ A.faces :=
    A.down_closed hC'_A Finset.subset_union_left (K.nonempty_of_mem σ hσ)
  have h_lk_apt : A.linkComplex σ hσA ∈ link_apts := by
    rw [h_link_apts]; exact ⟨A, hA_apt, hσA, rfl⟩
  have hC'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ C').mp hC'_max.1
  have hD'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ D').mp hD'_max.1
  exact ⟨A.linkComplex σ hσA, h_lk_apt,
    (SimplicialComplex.mem_linkComplex_iff A σ hσA C').mpr ⟨hC'_data.1, hC'_data.2.1, hC'_A⟩,
    (SimplicialComplex.mem_linkComplex_iff A σ hσA D').mpr ⟨hD'_data.1, hD'_data.2.1, hD'_A⟩⟩

/-- Thickness of the link: every facet $F'$ of the link is contained in at least three distinct
chambers, deduced from thickness of the ambient building applied to $\sigma \cup F'$. -/
theorem link_is_thick (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces) :
    ∀ F' C' : Finset V,
    (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' C' →
    (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C' →
    ∃ D₁ D₂ : Finset V,
      D₁ ≠ C' ∧ D₂ ≠ C' ∧ D₁ ≠ D₂ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₁ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₁ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsFacet F' D₂ ∧
      (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D₂ := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ
  intro F' C' hF'C' hC'_max
  have hF' := hF'C'.1.1
  have hF'_sub_C' := hF'C'.1.2.2
  have hF'_card := hF'C'.2
  have hF'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ F').mp hF'
  have hC'_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ C').mp hC'_max.1
  have hσC'_max := SimplicialComplex.union_maximal_of_linkComplex_maximal' hσ hC'_max
  have h_facet : K.IsFacet (σ ∪ F') (σ ∪ C') := by
    refine ⟨⟨hF'_data.2.2, hC'_data.2.2, Finset.union_subset_union_right hF'_sub_C'⟩, ?_⟩
    rw [SimplicialComplex.sdiff_union_eq_sdiff_of_disjoint' hF'_data.2.1 hC'_data.2.1]
    exact hF'_card
  obtain ⟨D₁, D₂, hD₁_ne, hD₂_ne, hD₁₂_ne, hD₁_facet, hD₁_max, hD₂_facet, hD₂_max⟩ :=
    b.thick (σ ∪ F') (σ ∪ C') h_facet hσC'_max
  have hσD₁ : σ ⊆ D₁ := Finset.subset_union_left.trans hD₁_facet.1.2.2
  have hσD₂ : σ ⊆ D₂ := Finset.subset_union_left.trans hD₂_facet.1.2.2
  have hD₁_ne_σ : (D₁ \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hF'_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hD₁_facet.1.2.2 (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hF'_data.2.1 hv⟩⟩
  have hD₂_ne_σ : (D₂ \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hF'_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hD₂_facet.1.2.2 (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hF'_data.2.1 hv⟩⟩
  have hD₁_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ D₁ hD₁_max.1 hσD₁ hD₁_ne_σ
  have hD₂_link := SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ D₂ hD₂_max.1 hσD₂ hD₂_ne_σ
  have hD₁_eq : σ ∪ (D₁ \ σ) = D₁ := Finset.union_sdiff_of_subset hσD₁
  have hD₂_eq : σ ∪ (D₂ \ σ) = D₂ := Finset.union_sdiff_of_subset hσD₂
  have hD₁_max_K : K.IsMaximal (σ ∪ (D₁ \ σ)) := by rw [hD₁_eq]; exact hD₁_max
  have hD₂_max_K : K.IsMaximal (σ ∪ (D₂ \ σ)) := by rw [hD₂_eq]; exact hD₂_max
  have hD₁_max_lk : lk.IsMaximal (D₁ \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hD₁_link hD₁_max_K
  have hD₂_max_lk : lk.IsMaximal (D₂ \ σ) :=
    SimplicialComplex.linkComplex_maximal_of_union_maximal' hσ hD₂_link hD₂_max_K
  have hF'_facet_D₁ : lk.IsFacet F' (D₁ \ σ) := by
    refine ⟨⟨hF', hD₁_link, ?_⟩, ?_⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hD₁_facet.1.2.2 (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hF'_data.2.1 hv⟩
    · have : (D₁ \ σ) \ F' = D₁ \ (σ ∪ F') := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [this]; exact hD₁_facet.2
  have hF'_facet_D₂ : lk.IsFacet F' (D₂ \ σ) := by
    refine ⟨⟨hF', hD₂_link, ?_⟩, ?_⟩
    · intro v hv
      exact Finset.mem_sdiff.mpr ⟨hD₂_facet.1.2.2 (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hF'_data.2.1 hv⟩
    · have : (D₂ \ σ) \ F' = D₂ \ (σ ∪ F') := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [this]; exact hD₂_facet.2
  refine ⟨D₁ \ σ, D₂ \ σ, ?_, ?_, ?_,
          hF'_facet_D₁, hD₁_max_lk, hF'_facet_D₂, hD₂_max_lk⟩
  · intro h_eq; apply hD₁_ne
    rw [← hD₁_eq, h_eq]
  · intro h_eq; apply hD₂_ne
    rw [← hD₂_eq, h_eq]
  · intro h_eq; apply hD₁₂_ne
    rw [← hD₁_eq, h_eq, hD₂_eq]



end Building
