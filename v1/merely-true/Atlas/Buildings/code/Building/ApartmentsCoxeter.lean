/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex

open ChamberComplex

variable {V : Type*} [DecidableEq V]

namespace Building

/-- Two simplicial complexes on $V$ are isomorphic if there is a bijection
$\varphi : V \to V$ that induces a bijection between their face sets. -/
def SimplicialComplexIso (A A' : SimplicialComplex V) : Prop :=
  ∃ φ : V → V,
    Function.Bijective φ ∧
    (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)

/-- An apartment $A$ has foldings if its underlying simplicial complex
extends to a chamber complex on which every pair of adjacent chambers
admits a pair of foldings collapsing one chamber onto the other. -/
def ApartmentHasFoldings (b : Building V) (A : SimplicialComplex V)
    (_hA : A ∈ b.apartmentSystem.apartments) : Prop :=
  ∃ (cc : ChamberComplex V),
    cc.toSimplicialComplex = A ∧
    ∀ C C' : Finset V,
      A.Adjacent C C' →
      ∃ (f f' : Folding cc),
        C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C ∧
        C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C'

/-- A maximal simplex (chamber) of an apartment $A$ is also a maximal
simplex of the ambient building. -/
theorem apartment_chamber_is_building_chamber (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hCmax : A.IsMaximal C) :
    b.toSimplicialComplex.IsMaximal C :=
  b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax

/-- If a face $C$ of an apartment $A$ is maximal in the ambient building,
then it is also maximal as a face of $A$. -/
theorem building_chamber_in_apartment_is_apartment_chamber (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_in_A : C ∈ A.faces)
    (hCmax : b.toSimplicialComplex.IsMaximal C) :
    A.IsMaximal C :=
  b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_in_A hCmax

/-- Every apartment of a building contains a chamber (maximal face). -/
theorem apartment_has_chamber (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ C : Finset V, C ∈ A.faces ∧ A.IsMaximal C := by

  obtain ⟨_, _, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA

  obtain ⟨s, hs⟩ := b.apartmentSystem.apt_nonempty A hA


  have hs_cc : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
  obtain ⟨C, hCmax_cc, _⟩ := cc.exists_maximal s hs_cc

  have hCmax_A : A.IsMaximal C := hcc_eq ▸ hCmax_cc
  exact ⟨C, hCmax_A.1, hCmax_A⟩

/-- Two apartments of a building that share a common chamber are
isomorphic as simplicial complexes. -/
theorem iso_exists_gives_iso (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (A' : SimplicialComplex V) (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hCA : C ∈ A.faces) (hCA' : C ∈ A'.faces) (hCmax : A.IsMaximal C) :
    SimplicialComplexIso A A' :=
  b.apartmentSystem.iso_bijective A hA A' hA' C hCA hCA' hCmax

/-- Simplicial complex isomorphism is transitive. -/
theorem simplicialComplexIso_trans :
    ∀ (A B A' : SimplicialComplex V),
    SimplicialComplexIso A B → SimplicialComplexIso B A' →
    SimplicialComplexIso A A' := by
  intro A B A' ⟨φ, hφ_bij, hφ_face⟩ ⟨ψ, hψ_bij, hψ_face⟩
  refine ⟨ψ ∘ φ, hψ_bij.comp hφ_bij, fun s => ?_⟩
  simp only [← Finset.image_image]
  exact (hφ_face s).trans (hψ_face _)

/-- All apartments of a building are pairwise isomorphic as simplicial
complexes. The proof uses that any two chambers lie in a common apartment
and that apartments sharing a chamber are isomorphic. -/
theorem AllApartmentsIsomorphic (b : Building V) :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ A' ∈ b.apartmentSystem.apartments,
        SimplicialComplexIso A A' := by
  intro A hA A' hA'
  obtain ⟨C, hCA, hCmaxA⟩ := apartment_has_chamber b A hA
  obtain ⟨C', hC'A', hC'maxA'⟩ := apartment_has_chamber b A' hA'
  have hCmax_bldg := apartment_chamber_is_building_chamber b A hA C hCmaxA
  have hC'max_bldg := apartment_chamber_is_building_chamber b A' hA' C' hC'maxA'
  obtain ⟨B, hB, hCB, hC'B⟩ := b.apartmentSystem.contains_pair C C' hCmax_bldg hC'max_bldg
  have hCmaxB := building_chamber_in_apartment_is_apartment_chamber b B hB C hCB hCmax_bldg
  have hC'maxB := building_chamber_in_apartment_is_apartment_chamber b B hB C' hC'B hC'max_bldg
  have hAB : SimplicialComplexIso A B :=
    iso_exists_gives_iso b A hA B hB C hCA hCB hCmaxA
  have hBA' : SimplicialComplexIso B A' :=
    iso_exists_gives_iso b B hB A' hA' C' hC'B hC'A' hC'maxB
  exact simplicialComplexIso_trans A B A' hAB hBA'

/-- The Coxeter type of a building: a Coxeter matrix $M$ together with the
data, for each apartment $A$, of a labeling of its chambers by the Coxeter
group $W(M)$ that is injective on chambers, surjective onto $W(M)$, and
sends adjacent chambers to $W(M)$-adjacent group elements. -/
structure CoxeterTypeOfBuilding (b : Building V) where
  B_idx : Type
  matrix : CoxeterMatrix B_idx
  apartments_iso : ∀ A ∈ b.apartmentSystem.apartments,
    ∃ (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → matrix.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : matrix.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' →
          CoxeterComplex.ChamberAdjacent matrix (φ C) (φ C'))

/-- Every apartment of a building is (canonically isomorphic to) a Coxeter
complex: there exist a Coxeter matrix $M$ and a thin chamber complex
structure whose chambers are in bijection with the Coxeter group $W(M)$
in an adjacency-preserving way. -/
theorem apartment_is_coxeter_complex (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → M.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
        cc.IsThin :=
  b.apartmentSystem.apt_is_coxeter A hA

/-- For an injective $f$, the image of a set difference equals the
difference of images: $f(s \setminus t) = f(s) \setminus f(t)$. -/
lemma finset_image_sdiff_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (s t : Finset α) (_hts : t ⊆ s) :
    (s \ t).image f = s.image f \ t.image f := by
  ext b
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨a, ⟨has, hat⟩, rfl⟩
    exact ⟨⟨a, has, rfl⟩, fun ⟨a', ha't, hfa'⟩ => hat (hf hfa' ▸ ha't)⟩
  · rintro ⟨⟨a, has, rfl⟩, hnot⟩
    exact ⟨a, ⟨has, fun hat => hnot ⟨a, hat, rfl⟩⟩, rfl⟩

/-- If $\varphi \circ \mathrm{inv} = \mathrm{id}$ pointwise, then applying
$\varphi$ to the $\mathrm{inv}$-image of $s$ recovers $s$. -/
lemma image_inv_image_eq {φ inv : V → V}
    (hright : ∀ v, φ (inv v) = v) (s : Finset V) :
    (s.image inv).image φ = s := by
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; rwa [hright]
  · intro hv; exact ⟨inv v, ⟨v, hv, rfl⟩, hright v⟩

/-- If $\mathrm{inv} \circ \varphi = \mathrm{id}$ pointwise, then applying
$\mathrm{inv}$ to the $\varphi$-image of $s$ recovers $s$. -/
lemma image_phi_image_eq {φ inv : V → V}
    (hleft : ∀ v, inv (φ v) = v) (s : Finset V) :
    (s.image φ).image inv = s := by
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; rwa [hleft]
  · intro hv; exact ⟨φ v, ⟨v, hv, rfl⟩, hleft v⟩

/-- Under a simplicial complex isomorphism $\varphi : A_0 \to A$ with
inverse $\mathrm{inv}$, the pullback by $\mathrm{inv}$ of a maximal face
of $A$ is a maximal face of $A_0$. -/
lemma iso_pullback_maximal {A₀ A : SimplicialComplex V}
    {φ inv : V → V}
    (hright : ∀ v, φ (inv v) = v)
    (hleft : ∀ v, inv (φ v) = v)
    (hφ_face : ∀ s, s ∈ A₀.faces ↔ s.image φ ∈ A.faces)
    (C : Finset V) (hCmax : A.IsMaximal C) :
    A₀.IsMaximal (C.image inv) := by
  constructor
  · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hCmax.1
  · intro y hy hsub
    have hy_A : y.image φ ∈ A.faces := (hφ_face y).mp hy
    have hsub' : C ⊆ y.image φ := by
      rw [← image_inv_image_eq hright C]
      exact Finset.image_subset_image hsub
    have := hCmax.2 _ hy_A hsub'
    rw [this]; exact image_phi_image_eq hleft y

/-- The Coxeter type of an apartment is preserved by simplicial
isomorphism: if an apartment $A_0$ carries a labeling by a Coxeter group
$W(M)$ realizing $A_0$ as the Coxeter complex of $M$, and $A_0 \cong A$,
then $A$ also carries such a labeling for the same Coxeter matrix $M$. -/
theorem iso_preserves_coxeter_type (b : Building V)
    (A₀ : SimplicialComplex V) (_hA₀ : A₀ ∈ b.apartmentSystem.apartments)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc₀ : ChamberComplex V) (_hcc₀ : cc₀.toSimplicialComplex = A₀)
    (φ₀ : Finset V → M.Group)
    (hinj₀ : ∀ C, A₀.IsMaximal C → ∀ D, A₀.IsMaximal D → φ₀ C = φ₀ D → C = D)
    (hsurj₀ : ∀ w : M.Group, ∃ C, A₀.IsMaximal C ∧ φ₀ C = w)
    (hadj₀ : ∀ C C', A₀.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ₀ C) (φ₀ C'))
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (hiso : SimplicialComplexIso A₀ A) :
    ∃ (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → M.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) := by

  obtain ⟨_, _, ccA, hccA_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA

  obtain ⟨φ_iso, hφ_bij, hφ_face⟩ := hiso

  have hφ_surj := hφ_bij.2
  let inv := Function.surjInv hφ_surj
  have hright : ∀ v, φ_iso (inv v) = v := Function.surjInv_eq hφ_surj
  have hleft : ∀ v, inv (φ_iso v) = v := fun v => hφ_bij.1 (hright (φ_iso v))
  have hinv_inj : Function.Injective inv := fun a b h => by
    have := congr_arg φ_iso h; rwa [hright, hright] at this

  refine ⟨ccA, hccA_eq, fun C => φ₀ (C.image inv), ?_, ?_, ?_⟩
  ·
    intro C hCmax D hDmax heq
    have hC_inv_max := iso_pullback_maximal hright hleft hφ_face C hCmax
    have hD_inv_max := iso_pullback_maximal hright hleft hφ_face D hDmax
    have := hinj₀ _ hC_inv_max _ hD_inv_max heq
    have h1 : (C.image inv).image φ_iso = (D.image inv).image φ_iso := by rw [this]
    rwa [image_inv_image_eq hright, image_inv_image_eq hright] at h1
  ·
    intro w
    obtain ⟨C₀, hC₀max, hC₀w⟩ := hsurj₀ w
    refine ⟨C₀.image φ_iso, ?_, ?_⟩
    ·
      constructor
      · exact (hφ_face C₀).mp hC₀max.1
      · intro y hy hsub
        have hy_A₀ : y.image inv ∈ A₀.faces := by
          rw [hφ_face]; rwa [image_inv_image_eq hright]
        have hsub' : C₀ ⊆ y.image inv := by
          rw [← image_phi_image_eq hleft C₀]
          exact Finset.image_subset_image hsub
        have h := hC₀max.2 _ hy_A₀ hsub'
        rw [← image_inv_image_eq hright y, ← h]
    ·
      show φ₀ ((C₀.image φ_iso).image inv) = w
      rw [image_phi_image_eq hleft, hC₀w]
  ·
    intro C C' hadj_A
    obtain ⟨hCmax, hC'max, hne, F, hFC, hFC'⟩ := hadj_A
    have hC_inv_max := iso_pullback_maximal hright hleft hφ_face C hCmax
    have hC'_inv_max := iso_pullback_maximal hright hleft hφ_face C' hC'max
    have hne_inv : C.image inv ≠ C'.image inv := by
      intro h
      apply hne
      have := congr_arg (Finset.image φ_iso) h
      rwa [image_inv_image_eq hright, image_inv_image_eq hright] at this

    have hF_inv_face_C : A₀.IsFacet (F.image inv) (C.image inv) := by
      refine ⟨⟨?_, ?_, Finset.image_subset_image hFC.1.2.2⟩, ?_⟩
      · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hFC.1.1
      · exact hC_inv_max.1
      · rw [← finset_image_sdiff_of_inj hinv_inj C F hFC.1.2.2,
             Finset.card_image_of_injective _ hinv_inj]
        exact hFC.2
    have hF_inv_face_C' : A₀.IsFacet (F.image inv) (C'.image inv) := by
      refine ⟨⟨?_, ?_, Finset.image_subset_image hFC'.1.2.2⟩, ?_⟩
      · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hFC'.1.1
      · exact hC'_inv_max.1
      · rw [← finset_image_sdiff_of_inj hinv_inj C' F hFC'.1.2.2,
             Finset.card_image_of_injective _ hinv_inj]
        exact hFC'.2
    exact hadj₀ _ _ ⟨hC_inv_max, hC'_inv_max, hne_inv,
      F.image inv, hF_inv_face_C, hF_inv_face_C'⟩

end Building
