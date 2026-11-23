/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.RetractionDef
import Atlas.Buildings.code.Building.RetractionProperties
import Atlas.Buildings.code.Building.Labels
import Atlas.Buildings.code.Building.VertexActionHelper

set_option maxHeartbeats 0

open scoped Classical

set_option maxHeartbeats 0


variable {V : Type} [DecidableEq V]

/-- Strict inclusion is preserved by the image of an injective function on
finite sets. -/
lemma finset_image_ssubset_of_injective {f : V → V} (hf : Function.Injective f)
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



/-- A bijective face-preserving map between apartments sends maximal faces
to maximal faces. -/
lemma bijective_face_iso_preserves_maximal
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





