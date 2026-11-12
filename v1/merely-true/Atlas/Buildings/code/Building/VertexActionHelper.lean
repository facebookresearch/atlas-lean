/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
import Mathlib.GroupTheory.Coxeter.Basic

open scoped Classical

set_option maxHeartbeats 4000000

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- Two functions $r, f$ agreeing on a superset $E \supseteq s$ produce the
same image on $s$. -/
lemma finset_image_eq_of_agree {s E : Finset V} {r f : V → V} (hsE : s ⊆ E)
    (heq : ∀ v ∈ E, r v = f v) : s.image r = s.image f := by
  ext x; simp only [Finset.mem_image]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [← heq y (hsE hy)]; exact h⟩,
         fun ⟨y, hy, h⟩ => ⟨y, hy, by rw [heq y (hsE hy)]; exact h⟩⟩

/-- On a face fixed by the folding $f$, the wall reflection $s$ agrees with
the opposite folding $g$. -/
lemma wallReflection_eq_g_on_fixed {X : ChamberComplex V} (wr : WallReflection X)
    {E : Finset V} (hfE : E.image wr.rf.f.morph.toFun = E) :
    ∀ v ∈ E, wr.refl v = wr.rf.g.morph.toFun v := by
  intro v hv
  have hfv : wr.rf.f.morph.toFun v = v := wr.rf.f.fixes_pointwise hfE v hv


  show reflectionFun wr.rf v = wr.rf.g.morph.toFun v
  simp only [reflectionFun, hfv, ite_true]

/-- On a face moved by the folding $f$, the wall reflection agrees with $f$. -/
lemma wallReflection_eq_f_on_moved {X : ChamberComplex V} (wr : WallReflection X)
    {E : Finset V} (hEmax : X.toSimplicialComplex.IsMaximal E)
    (hfE : E.image wr.rf.f.morph.toFun ≠ E) :
    ∀ v ∈ E, wr.refl v = wr.rf.f.morph.toFun v := by

  have hE_in_f_moved : E ∈ wr.rf.f.movedChambers := ⟨hEmax, hfE⟩
  have hE_in_g_fixed : E ∈ wr.rf.g.fixedChambers :=
    wr.rf.complementary_moved ▸ hE_in_f_moved
  have hgE : E.image wr.rf.g.morph.toFun = E := hE_in_g_fixed.2
  intro v hv
  have hgv : wr.rf.g.morph.toFun v = v := wr.rf.g.fixes_pointwise hgE v hv
  show reflectionFun wr.rf v = wr.rf.f.morph.toFun v
  simp only [reflectionFun]
  by_cases hfv : wr.rf.f.morph.toFun v = v
  · simp [hfv, hgv]
  · simp [hfv]

/-- A wall reflection acts on faces of the chamber complex, sending faces
to faces. -/
theorem wallReflection_maps_faces {X : ChamberComplex V} (wr : WallReflection X)
    (s : Finset V) (hs : s ∈ X.toSimplicialComplex.faces) :
    s.image wr.refl ∈ X.toSimplicialComplex.faces := by
  obtain ⟨E, hEmax, hsE⟩ := X.exists_maximal s hs
  by_cases hfE : E.image wr.rf.f.morph.toFun = E
  ·
    rw [finset_image_eq_of_agree hsE (wallReflection_eq_g_on_fixed wr hfE)]
    exact wr.rf.g.morph.map_face s hs
  ·
    rw [finset_image_eq_of_agree hsE (wallReflection_eq_f_on_moved wr hEmax hfE)]
    exact wr.rf.f.morph.map_face s hs

/-- The composition of a list of bijective functions is bijective. -/
lemma list_comp_bijective :
    ∀ (fs : List (V → V)), (∀ f ∈ fs, Function.Bijective f) →
      Function.Bijective (fs.foldr (· ∘ ·) id)
  | [], _ => Function.bijective_id
  | f :: fs, h => by
    rw [List.foldr_cons]
    have hf : Function.Bijective f := h f (List.mem_cons.mpr (Or.inl rfl))
    have hfs := list_comp_bijective fs (fun g hg => h g (List.mem_cons.mpr (Or.inr hg)))
    exact hf.comp hfs

/-- The wall reflection sends the chamber $D$ across the panel to the
opposite chamber $C$. -/
lemma wallReflection_maps_chamber {X : ChamberComplex V} (wr : WallReflection X)
    {C D : Finset V}
    (hDmax : X.toSimplicialComplex.IsMaximal D)
    (hfC : C.image wr.rf.f.morph.toFun = C)
    (hfD : D.image wr.rf.f.morph.toFun = C)
    (hne : C ≠ D) :
    D.image wr.refl = C := by
  have hfD_ne : D.image wr.rf.f.morph.toFun ≠ D := by
    intro h; rw [hfD] at h; exact hne h

  rw [finset_image_eq_of_agree (Finset.Subset.refl D)
      (wallReflection_eq_f_on_moved wr hDmax hfD_ne)]
  exact hfD

/-- Compose a sequence of vertex maps witnessing the steps of a gallery
chain into a single composed map. -/
theorem chain_compose
    {faces : Set (Finset V)}
    {R : Finset V → Finset V → Prop}
    (l : List (Finset V))
    (hchain : List.IsChain R l)
    (hmaps : ∀ x y, R x y → ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s ∈ faces, s.image φ ∈ faces) ∧
      (∀ s, s.image φ ∈ faces → s ∈ faces) ∧
      x.image φ = y) :
    ∀ (hne : l ≠ []),
    ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s ∈ faces, s.image φ ∈ faces) ∧
      (∀ s, s.image φ ∈ faces → s ∈ faces) ∧
      (l.head hne).image φ = l.getLast hne := by
  induction hchain with
  | nil => intro h; exact absurd rfl h
  | singleton a =>
    intro _
    exact ⟨id, Function.bijective_id,
      fun s hs => by simp [hs],
      fun s hs => by simp at hs; exact hs,
      by simp⟩
  | cons_cons hab htl ih =>
    rename_i a b rest
    intro hne
    obtain ⟨φ₁, hbij₁, hpres₁, hback₁, himg₁⟩ := hmaps a b hab
    have hne_tl : (b :: rest) ≠ [] := List.cons_ne_nil b rest
    obtain ⟨φ₂, hbij₂, hpres₂, hback₂, himg₂⟩ := ih hne_tl
    refine ⟨φ₂ ∘ φ₁, hbij₂.comp hbij₁, ?_, ?_, ?_⟩
    ·
      intro s hs
      have : s.image (φ₂ ∘ φ₁) = (s.image φ₁).image φ₂ := (Finset.image_image ..).symm
      rw [this]
      exact hpres₂ _ (hpres₁ s hs)
    ·
      intro s hs
      have : s.image (φ₂ ∘ φ₁) = (s.image φ₁).image φ₂ := (Finset.image_image ..).symm
      rw [this] at hs
      exact hback₁ _ (hback₂ _ hs)
    ·
      simp only [List.head_cons]
      have : a.image (φ₂ ∘ φ₁) = (a.image φ₁).image φ₂ := (Finset.image_image ..).symm
      rw [this, himg₁]
      have hlast : (a :: b :: rest).getLast hne = (b :: rest).getLast hne_tl :=
        List.getLast_cons hne_tl
      rw [hlast]
      exact himg₂

/-- Vertex-level automorphism of an apartment: a bijective vertex map
realising chamber transitivity. -/
theorem apt_vertex_level_automorphism
    (A : SimplicialComplex V) (cc : ChamberComplex V)
    (hcc : cc.toSimplicialComplex = A)
    (hWR : ∀ C D : Finset V, A.Adjacent C D →
      ∃ wr : WallReflection cc, D.image wr.refl = C)
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C := by

  have hD_cc : cc.toSimplicialComplex.IsMaximal D := hcc ▸ hD
  have hC_cc : cc.toSimplicialComplex.IsMaximal C := hcc ▸ hC
  obtain ⟨gal, hstart, hend⟩ := cc.gallery_connected D C hD_cc hC_cc

  have hne : gal.chambers ≠ [] := by
    intro h; rw [h] at hstart; simp at hstart
  have hhead : gal.chambers.head hne = D := by
    have := List.head?_eq_some_head hne
    rw [this] at hstart
    exact Option.some_injective _ hstart
  have hlast : gal.chambers.getLast hne = C := by
    rw [List.getLast?_eq_some_getLast hne] at hend
    exact Option.some_injective _ hend

  have hchain_A : List.IsChain A.Adjacent gal.chambers := by
    have := gal.adjacent_consecutive
    exact this.imp (fun _ _ h => hcc ▸ h)


  have hmaps : ∀ x y, A.Adjacent x y → ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s ∈ A.faces, s.image φ ∈ A.faces) ∧
      (∀ s, s.image φ ∈ A.faces → s ∈ A.faces) ∧
      x.image φ = y := by
    intro x y hxy

    obtain ⟨wr, himg⟩ := hWR x y hxy

    use wr.refl
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      exact (Function.Involutive.bijective (fun v => wr.refl_involutive v))
    ·
      intro s hs
      rw [← hcc] at hs ⊢
      exact wallReflection_maps_faces wr s hs
    ·
      intro s hs
      rw [← hcc] at hs ⊢
      have hinv : s = (s.image wr.refl).image wr.refl := by
        rw [Finset.image_image,
          show wr.refl ∘ wr.refl = id from funext wr.refl_involutive, Finset.image_id]
      rw [hinv]
      exact wallReflection_maps_faces wr _ hs
    ·


      calc x.image wr.refl
          = (y.image wr.refl).image wr.refl := by rw [himg]
        _ = y.image (wr.refl ∘ wr.refl) := Finset.image_image ..
        _ = y.image id := by rw [show wr.refl ∘ wr.refl = id from funext wr.refl_involutive]
        _ = y := Finset.image_id

  obtain ⟨φ, hbij, hpres, hback, himg⟩ := chain_compose gal.chambers hchain_A hmaps hne
  exact ⟨φ, hbij, fun s => ⟨hpres s, hback s⟩, by rw [hhead] at himg; rw [hlast] at himg; exact himg⟩

end ChamberComplex




