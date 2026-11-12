/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Uniqueness

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- `f` *fixes $C$ pointwise*: $f(v) = v$ for every $v \in C$. -/
def FixesPointwise
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (C : Finset V) : Prop :=
  ∀ v ∈ C, f.toFun v = v

/-- The image of a gallery under $f$ *stutters*: some adjacent pair of chambers in the list has
equal $f$-images. -/
def ImageGalleryStutters
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (cs : List (Finset V)) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < cs.length),
    (cs.get ⟨i, by omega⟩).image f.toFun =
    (cs.get ⟨i + 1, hi⟩).image f.toFun

/-- Equivalence between the two formulations of "the image gallery stutters". -/
lemma imageGalleryStutters_iff_galleryStuttersUnder
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (cs : List (Finset V)) :
    ImageGalleryStutters f cs ↔
    SimplicialComplex.GalleryStuttersUnder cs f.toFun := by
  unfold ImageGalleryStutters SimplicialComplex.GalleryStuttersUnder
  constructor
  · rintro ⟨i, hi, heq⟩
    rw [List.isChain_iff_getElem]
    push Not
    refine ⟨i, by simp only [List.length_map]; exact hi, ?_⟩
    simp only [List.getElem_map]
    exact heq
  · intro hstut
    obtain ⟨n, hn, hne⟩ := List.exists_not_getElem_of_not_isChain hstut
    simp only [List.getElem_map, List.length_map, not_ne_iff] at hn hne
    exact ⟨n, hn, hne⟩

/-- *Book's uniqueness lemma (3.3/3.5)*: in a thin chamber complex, if $f$ is a chamber map
fixing the starting chamber $C_0$ pointwise, then along any gallery $\gamma$ starting at $C_0$,
either $f \circ \gamma$ stutters or $f$ fixes every chamber of $\gamma$ pointwise. -/
theorem uniqueness_lemma_book
    {K : ChamberComplex V}
    (hThin : K.IsThin)
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (hfCM : f.IsChamberMap)
    (C₀ : Finset V) (_hC₀ : K.toSimplicialComplex.IsMaximal C₀)
    (hfix₀ : FixesPointwise f C₀)
    (γ : Gallery K.toSimplicialComplex)
    (hstart : γ.chambers.head? = some C₀) :
    ImageGalleryStutters f γ.chambers ∨
    (∀ C ∈ γ.chambers, FixesPointwise f C) := by
  have h := SimplicialComplex.uniqueness_lemma hThin f hfCM C₀ _hC₀ hfix₀ γ hstart
  rcases h with hstut | hfix
  · left
    rwa [imageGalleryStutters_iff_galleryStuttersUnder]
  · right
    intro C hC v hv
    exact hfix C hC v hv

end ChamberComplex
