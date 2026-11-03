/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- The combinatorial *Coxeter properties* of a chamber complex: thinness plus, for every
adjacent pair $C \sim D$, a folding that fixes $C$ and sends $D$ to $C$. -/
structure CoxeterProperties (K : ChamberComplex V) where
  thin : K.IsThin
  folding_maps_adj_to_self : ∀ C D, K.toSimplicialComplex.Adjacent C D →
    ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C

/-- Two chambers $C, D$ are *separated by a wall* if some reversible folding places them on
opposite sides. -/
def SeparatedByWall (K : ChamberComplex V) (C D : Finset V) : Prop :=
  ∃ rf : ReversibleFolding K,
    OppositeSides rf.f C D

/-- $K$ is a *Coxeter complex*: it carries a bijective labelling $\varphi : \text{chambers} \to W$
into a Coxeter group $W$ such that adjacency corresponds to right multiplication by a simple
generator, every facet is shared by at least one other chamber. -/
def IsCoxeterComplex (K : ChamberComplex V) : Prop :=
  ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
    (∀ C, K.toSimplicialComplex.IsMaximal C →
      ∀ D, K.toSimplicialComplex.IsMaximal D →
        φ C = φ D → C = D) ∧
    (∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w) ∧
    (∀ C C', K.toSimplicialComplex.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
    (∀ C C', K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C') →
        K.toSimplicialComplex.Adjacent C C') ∧
    (∀ F C, K.toSimplicialComplex.IsFacet F C →
      K.toSimplicialComplex.IsMaximal C →
      ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsMaximal D ∧
        K.toSimplicialComplex.IsFacet F D)

/-- $K$ *has sufficient reversible foldings*: every adjacent pair admits a reversible folding
swapping them as boundary chambers of the wall. -/
def HasSufficientReversibleFoldings (K : ChamberComplex V) : Prop :=
  ∀ C D : Finset V,
    K.toSimplicialComplex.Adjacent C D →
    ∃ (rf : ReversibleFolding K),
      C.image rf.f.morph.toFun = C ∧ D.image rf.f.morph.toFun = C ∧
      D.image rf.g.morph.toFun = D ∧ C.image rf.g.morph.toFun = D

/-- Sufficient reversible foldings give the "folding maps adjacent to self" condition. -/
theorem hasSufficientReversibleFoldings_folding_maps_adj_to_self
    (K : ChamberComplex V) (hSRF : HasSufficientReversibleFoldings K) :
    ∀ C D, K.toSimplicialComplex.Adjacent C D →
      ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C := by
  intro C D hadj
  obtain ⟨rf, hfC, hfD_eq_C, _, _⟩ := hSRF C D hadj
  exact ⟨rf.f, hfC, hfD_eq_C⟩

/-- Assemble `CoxeterProperties K` from thinness plus sufficient reversible foldings. -/
def coxeterProperties_of_hasSufficientReversibleFoldings
    (K : ChamberComplex V) (hThin : K.IsThin)
    (hSRF : HasSufficientReversibleFoldings K) : CoxeterProperties K where
  thin := hThin
  folding_maps_adj_to_self :=
    hasSufficientReversibleFoldings_folding_maps_adj_to_self K hSRF

/-- Sufficient reversible foldings imply that every adjacent pair is separated by a wall. -/
theorem hasSufficientReversibleFoldings_separatedByWall
    (K : ChamberComplex V) (hSRF : HasSufficientReversibleFoldings K)
    (C D : Finset V) (hadj : K.toSimplicialComplex.Adjacent C D) :
    SeparatedByWall K C D := by
  obtain ⟨rf, hfC, hfD_eq_C, _, _⟩ := hSRF C D hadj
  have hne : C ≠ D := hadj.2.2.1
  have hfD_ne : D.image rf.f.morph.toFun ≠ D := by
    intro h; rw [hfD_eq_C] at h; exact hne h
  exact ⟨rf, Or.inl ⟨hfC, hfD_ne⟩⟩

/-- Converse: in a thin complex, "adjacent chambers separated by a wall" implies sufficient
reversible foldings. -/
theorem separatedByWall_hasSufficientReversibleFoldings
    (K : ChamberComplex V) (hThin : K.IsThin)
    (hSep : ∀ C D, K.toSimplicialComplex.Adjacent C D → SeparatedByWall K C D) :
    HasSufficientReversibleFoldings K := by
  intro C D hadj
  obtain ⟨rf, hopp⟩ := hSep C D hadj
  rcases hopp with ⟨hfC, hfD_ne⟩ | ⟨hfD, hfC_ne⟩
  ·
    have hfD_eq_C : D.image rf.f.morph.toFun = C :=
      Folding.fold_adj_to_self rf.f hThin hadj hfC hfD_ne
    have hgC_ne : C.image rf.g.morph.toFun ≠ C := by
      intro h
      have hC_in_g_fixed : C ∈ rf.g.fixedChambers := ⟨hadj.1, h⟩
      have hC_in_f_fixed : C ∈ rf.f.fixedChambers := ⟨hadj.1, hfC⟩
      exact rf.halves_disjoint C ⟨hC_in_f_fixed, hC_in_g_fixed⟩
    have hgD : D.image rf.g.morph.toFun = D := by
      have hD_in_f_moved : D ∈ rf.f.movedChambers := ⟨hadj.2.1, hfD_ne⟩
      have hD_in_g_fixed : D ∈ rf.g.fixedChambers :=
        rf.complementary_moved ▸ hD_in_f_moved
      exact hD_in_g_fixed.2
    have hadj' : K.toSimplicialComplex.Adjacent D C := by
      obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
      exact ⟨hDmax, hCmax, hne.symm, F, hFD, hFC⟩
    have hgC_eq_D : C.image rf.g.morph.toFun = D :=
      Folding.fold_adj_to_self rf.g hThin hadj' hgD hgC_ne
    exact ⟨rf, hfC, hfD_eq_C, hgD, hgC_eq_D⟩
  ·
    have hadj' : K.toSimplicialComplex.Adjacent D C := by
      obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
      exact ⟨hDmax, hCmax, hne.symm, F, hFD, hFC⟩
    have hfC_eq_D : C.image rf.f.morph.toFun = D :=
      Folding.fold_adj_to_self rf.f hThin hadj' hfD hfC_ne
    have hgD_ne : D.image rf.g.morph.toFun ≠ D := by
      intro h
      have hD_in_g_fixed : D ∈ rf.g.fixedChambers := ⟨hadj.2.1, h⟩
      have hD_in_f_fixed : D ∈ rf.f.fixedChambers := ⟨hadj.2.1, hfD⟩
      exact rf.halves_disjoint D ⟨hD_in_f_fixed, hD_in_g_fixed⟩
    have hgC : C.image rf.g.morph.toFun = C := by
      have hC_in_f_moved : C ∈ rf.f.movedChambers := ⟨hadj.1, hfC_ne⟩
      have hC_in_g_fixed : C ∈ rf.g.fixedChambers :=
        rf.complementary_moved ▸ hC_in_f_moved
      exact hC_in_g_fixed.2
    have hgD_eq_C : D.image rf.g.morph.toFun = C :=
      Folding.fold_adj_to_self rf.g hThin hadj hgC hgD_ne

    let rf' : ReversibleFolding K := {
      f := rf.g
      g := rf.f
      complementary_fixed := rf.complementary_moved.symm
      complementary_moved := rf.complementary_fixed.symm
      opposite_action := rf.opposite_action'
      opposite_action' := rf.opposite_action
    }
    exact ⟨rf', hgC, hgD_eq_C, hfD, hfC_eq_D⟩

/-- Sufficient reversible foldings imply the (one-sided) "sufficient foldings" condition used in
the Tits/AptIsCoxeter proof. -/
theorem hasSufficientReversibleFoldings_hasSufficientFoldings
    (K : ChamberComplex V) (hSRF : HasSufficientReversibleFoldings K) :
    AptIsCoxeterProof.HasSufficientFoldings K := by
  intro C C' hadj
  obtain ⟨rf, hfC, hfC'_eq_C, hgC', hgC_eq_C'⟩ := hSRF C C' hadj
  exact ⟨rf.f, rf.g, hfC, hfC'_eq_C, hgC', hgC_eq_C'⟩




/-- An injective vertex map sends distinct chambers to distinct image chambers. -/
lemma injective_image_ne_of_ne
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (hinj : Function.Injective f.toFun)
    {C D : Finset V}
    (_hC : C ∈ K.toSimplicialComplex.faces)
    (_hD : D ∈ K.toSimplicialComplex.faces)
    (hne : C ≠ D) :
    C.image f.toFun ≠ D.image f.toFun := by
  intro heq
  apply hne
  ext v
  constructor
  · intro hv
    have : f.toFun v ∈ D.image f.toFun := by
      rw [← heq]; exact Finset.mem_image_of_mem _ hv
    rw [Finset.mem_image] at this
    obtain ⟨w, hw, hfw⟩ := this
    exact hinj hfw ▸ hw
  · intro hv
    have : f.toFun v ∈ C.image f.toFun := by
      rw [heq]; exact Finset.mem_image_of_mem _ hv
    rw [Finset.mem_image] at this
    obtain ⟨w, hw, hfw⟩ := this
    exact hinj hfw ▸ hw

/-- The image of a gallery under an injective map never stutters. -/
lemma injective_no_stutter
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (hinj : Function.Injective f.toFun)
    (γ : Gallery K.toSimplicialComplex) :
    ¬ ImageGalleryStutters f γ.chambers := by
  intro ⟨i, hi, heq⟩

  let fi : Fin γ.chambers.length := ⟨i, by omega⟩
  let fi1 : Fin γ.chambers.length := ⟨i + 1, hi⟩

  have hC_mem : γ.chambers.get fi ∈ γ.chambers := List.get_mem γ.chambers fi
  have hD_mem : γ.chambers.get fi1 ∈ γ.chambers := List.get_mem γ.chambers fi1
  have hC_max := γ.all_maximal _ hC_mem
  have hD_max := γ.all_maximal _ hD_mem

  have hchain := γ.adjacent_consecutive
  have hadj : K.toSimplicialComplex.Adjacent (γ.chambers.get fi) (γ.chambers.get fi1) := by
    rw [List.isChain_iff_getElem] at hchain
    have := hchain i hi
    simp only [List.get_eq_getElem] at this ⊢
    exact this

  have hne : γ.chambers.get fi ≠ γ.chambers.get fi1 := hadj.2.2.1
  exact injective_image_ne_of_ne f hinj hC_max.1 hD_max.1 hne heq

end ChamberComplex
