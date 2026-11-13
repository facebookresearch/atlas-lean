/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.UniqueRetraction

open SimplicialComplex in
/-- If $\tau$ is a maximal face of the link $\mathrm{lk}_K(\sigma)$, then $\sigma \cup \tau$ is a
maximal face of the ambient complex $K$. -/
theorem union_maximal_of_linkComplex_maximal_helper {V : Type*} [DecidableEq V]
    {K : SimplicialComplex V} {σ : Finset V}
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

variable {V : Type} [DecidableEq V]


/-- Pushing forward a strict inclusion of finite sets along an injective map yields a strict
inclusion of images. -/
lemma finset_image_ssubset_of_injective' {f : V → V} (hf : Function.Injective f)
    {s t : Finset V} (h : s ⊂ t) : s.image f ⊂ t.image f := by
  constructor
  · exact Finset.image_subset_image h.1
  · intro heq
    apply h.2
    intro x hx
    have : f x ∈ s.image f := by
      apply heq
      exact Finset.mem_image_of_mem f hx
    rw [Finset.mem_image] at this
    obtain ⟨y, hy, hfy⟩ := this
    have := hf hfy; subst this; exact hy

/-- A bijective simplicial isomorphism $\varphi : A \to A'$ carries maximal faces of $A$ to maximal
faces of $A'$. -/
lemma bijective_face_iso_preserves_maximal'
    {A A' : SimplicialComplex V} {φ : V → V} (hφ_bij : Function.Bijective φ)
    (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
    {s : Finset V} (hs : A.IsMaximal s) : A'.IsMaximal (s.image φ) := by
  constructor
  · exact (hφ_faces s).mp hs.1
  · intro t ht hsub
    set t₀ := t.preimage φ (hφ_bij.1.injOn) with ht₀_def
    have mem_t₀ : ∀ x, x ∈ t₀ ↔ φ x ∈ t := fun x => Finset.mem_preimage
    have ht₀_img : t₀.image φ = t := by
      ext z; constructor
      · rw [Finset.mem_image]; rintro ⟨w, hw, rfl⟩; exact (mem_t₀ w).mp hw
      · intro hz
        obtain ⟨w, rfl⟩ := hφ_bij.2 z
        exact Finset.mem_image_of_mem φ ((mem_t₀ w).mpr hz)
    have ht₀_face : t₀ ∈ A.faces := by
      rw [← ht₀_img] at ht; exact (hφ_faces t₀).mpr ht
    have hs_sub_t₀ : s ⊆ t₀ := by
      intro x hx; exact (mem_t₀ x).mpr (hsub (Finset.mem_image_of_mem φ hx))
    have hs_eq : s = t₀ := hs.2 t₀ ht₀_face hs_sub_t₀
    rw [← ht₀_img, ← hs_eq]


