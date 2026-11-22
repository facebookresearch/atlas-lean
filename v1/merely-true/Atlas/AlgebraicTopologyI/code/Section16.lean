/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Atlas.AlgebraicTopologyI.code.Section15
import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.Section10
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian

namespace CWComplex

variable (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- **Definition 16.1.** The group of cellular `n`-chains of a CW complex `X`, defined as the
free abelian group on the set of `n`-cells of `X`. -/
abbrev cellularChains (n : ℕ) : Type _ :=
  FreeAbelianGroup (cells X n)






section SkeletonPair

variable [T2Space X]

/-- The previous skeleton `X_{n-1}` for `n ≥ 1`, and the empty set for `n = 0`. Convenient
shorthand used for forming the CW-pair `(X_n, X_{n-1})`. -/
noncomputable def prevSkeleton (n : ℕ) : Set X :=
  match n with
  | 0 => ∅
  | k + 1 => ↑(skeleton X k)


end SkeletonPair

end CWComplex

open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI

noncomputable section


namespace CWComplex.SkeletonHomology

variable (X : Type) [TopologicalSpace X] [T2Space X]
variable [Topology.CWComplex (Set.univ : Set X)]

/-- The continuous inclusion of the `k`-skeleton `X_k ↪ X`, viewed as a morphism in `TopCat`. -/
def skeletonInclusion (k : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X k : Set X) ⟶ TopCat.of X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The map on singular homology `H_q(X_k) → H_q(X)` induced by the inclusion of the
`k`-skeleton. -/
def skeletonHomologyMap (q k : ℕ) :
    SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) ⟶
    SingularHomologyGroup q X :=
  ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
    (skeletonInclusion X k)

/-- The one-step skeleton inclusion `X_k ↪ X_{k+1}`, viewed as a morphism in `TopCat`. -/
def skeletonStepInclusion (k : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X k : Set X) ⟶
    TopCat.of ↥(CWComplex.skeleton X (k + 1) : Set X) :=
  ⟨Set.inclusion (Topology.RelCWComplex.skeleton_mono (by norm_cast; omega)),
   continuous_inclusion _⟩

/-- The map on singular homology `H_q(X_k) → H_q(X_{k+1})` induced by the one-step
skeleton inclusion. -/
def skeletonStepHomologyMap (q k : ℕ) :
    SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) ⟶
    SingularHomologyGroup q ↥(CWComplex.skeleton X (k + 1) : Set X) :=
  ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
    (skeletonStepInclusion X k)

/-- The inclusion `X_k ↪ X` factors through the one-step inclusion `X_k ↪ X_{k+1}`. -/
lemma skeletonInclusion_factor (k : ℕ) :
    skeletonInclusion X k =
    skeletonStepInclusion X k ≫ skeletonInclusion X (k + 1) := by
  ext x; rfl

/-- Functoriality: the homology map `H_q(X_k) → H_q(X)` factors through `H_q(X_{k+1})`. -/
lemma skeletonHomologyMap_factor (q k : ℕ) :
    skeletonHomologyMap X q k =
    skeletonStepHomologyMap X q k ≫ skeletonHomologyMap X q (k + 1) := by
  show ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
      (skeletonInclusion X k) =
    ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
      (skeletonStepInclusion X k) ≫
    ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ)).map
      (skeletonInclusion X (k + 1))
  rw [← Functor.map_comp, ← skeletonInclusion_factor]

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/-- The `0`-skeleton is disjoint from any open cell of positive dimension. -/
lemma skeleton_zero_inter_openCell_empty
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    {n : ℕ} (hn : n ≥ 1)
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) n) :
    (CWComplex.skeleton X 0 : Set X) ∩ Topology.RelCWComplex.openCell n j = ∅ := by
  have hni : j ∉ (CWComplex.skeleton X 0 : Topology.RelCWComplex.Subcomplex _).I n := by
    simp only [CWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
               Topology.RelCWComplex.Subcomplex.mk', Set.mem_setOf_eq]
    push Not
    exact_mod_cast hn
  have := Topology.RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem
    (CWComplex.skeleton X 0 : Topology.RelCWComplex.Subcomplex _) hni
  rw [Set.disjoint_iff_inter_eq_empty] at this
  rw [Set.inter_comm]; exact this

/-- The intersection of the `0`-skeleton with any closed cell of `X` is a finite set. -/
lemma skeleton_zero_inter_closedCell_finite
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    ∀ (n : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set X) n),
    Set.Finite ((CWComplex.skeleton X 0 : Set X) ∩
                Topology.RelCWComplex.closedCell n j) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j
    by_cases hn : n = 0
    · subst hn
      have : Topology.RelCWComplex.closedCell (C := Set.univ) 0 j =
        {(Topology.RelCWComplex.map (C := Set.univ) 0 j : PartialEquiv (Fin 0 → ℝ) X)
          default} := by
        ext y
        simp only [Topology.RelCWComplex.closedCell, Set.mem_image, Metric.mem_closedBall,
                    Set.mem_singleton_iff]
        constructor
        · rintro ⟨z, _, rfl⟩
          congr 1
          exact Subsingleton.elim z default
        · rintro rfl
          exact ⟨default, by simp [Subsingleton.elim (default : Fin 0 → ℝ) 0], rfl⟩
      rw [this]
      exact Set.Finite.subset (Set.finite_singleton _) Set.inter_subset_right
    · have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
      rw [Set.inter_union_distrib_left]
      apply Set.Finite.union
      · obtain ⟨I, hI⟩ := Topology.CWComplex.cellFrontier_subset_finite_closedCell
          (C := Set.univ) n j
        apply Set.Finite.subset _ (Set.inter_subset_inter_right _ hI)
        rw [Set.inter_iUnion₂]
        apply Set.Finite.biUnion
          ((Set.finite_Iio n).subset fun _ hm => hm)
        intro m hm
        rw [Set.inter_iUnion₂]
        apply Set.Finite.biUnion (I m).finite_toSet
        intro j' _
        exact ih m hm j'
      · rw [skeleton_zero_inter_openCell_empty hn1 j]
        exact Set.finite_empty

/-- Every subset of the `0`-skeleton of a CW complex is closed in `X` (the `0`-skeleton
inherits the discrete topology). -/
lemma isClosed_subset_skeleton_zero
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (A : Set X) (hA : A ⊆ (CWComplex.skeleton X 0 : Set X)) :
    IsClosed A := by
  apply Topology.CWComplex.closed' A (Set.subset_univ A)
  intro n j
  exact (Set.Finite.subset (skeleton_zero_inter_closedCell_finite n j)
    (Set.inter_subset_inter_left _ hA)).isClosed

/-- The `0`-skeleton of a CW complex is totally disconnected (in fact, discrete). -/
lemma skeleton_zero_totallyDisconnected
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    TotallyDisconnectedSpace ↥(CWComplex.skeleton X 0 : Set X) := by
  have : DiscreteTopology ↥(CWComplex.skeleton X 0 : Set X) := by
    rw [discreteTopology_iff_forall_isClosed]
    intro s
    rw [isClosed_induced_iff]
    refine ⟨Subtype.val '' s, ?_, ?_⟩
    · apply isClosed_subset_skeleton_zero
      intro x hx
      obtain ⟨⟨y, hy⟩, _, hyx⟩ := hx
      rw [← hyx]; exact hy
    · ext ⟨x, hx⟩
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨⟨y, hy⟩, hys, hyx⟩
        have : (⟨y, hy⟩ : ↥(CWComplex.skeleton X 0 : Set X)) = ⟨x, hx⟩ :=
          Subtype.ext hyx
        rwa [this] at hys
      · intro hxs
        exact ⟨⟨x, hx⟩, hxs, rfl⟩
  infer_instance

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology




/-- Long exact sequence argument: if both `H_q(X_k) = 0` and the relative
homology `H_q(X_{k+1}, X_k) = 0`, then `H_q(X_{k+1}) = 0`. -/
theorem les_pair_isZero
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (q k : ℕ)
    (hk : IsZero (SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X)))
    (hrel : IsZero (Excision.RelativeSingularHomologyGroup q
      ↥(CWComplex.skeleton X (k + 1) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))) :
    IsZero (SingularHomologyGroup q ↥(CWComplex.skeleton X (k + 1) : Set X)) := by

  let Y : Type := ↥(CWComplex.skeleton X (k + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)

  have hse := Excision.bottomSES_shortExact Y A

  have hexact := hse.homology_exact₂ q

  have hrel' : IsZero ((Excision.bottomSES Y A).X₃.homology q) := hrel
  have hg_zero : HomologicalComplex.homologyMap (Excision.bottomSES Y A).g q = 0 :=
    hrel'.eq_of_tgt _ _

  have hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X k : Set X) :=
    { toEquiv := {
        toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
            (by norm_cast; omega) hx⟩, hx⟩
        left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
        right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  have hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X k : Set X) :=
    TopCat.isoOfHomeo hA_homeo

  have hchain_iso : Excision.singularChainZ.obj (TopCat.of ↥A) ≅
      Excision.singularChainZ.obj (TopCat.of ↥(CWComplex.skeleton X k : Set X)) :=
    Excision.singularChainZ.mapIso hA_iso

  have hhom_iso : (Excision.bottomSES Y A).X₁.homology q ≅
      SingularHomologyGroup q ↥(CWComplex.skeleton X k : Set X) :=
    (HomologicalComplex.homologyFunctor _ _ q).mapIso hchain_iso

  have hA_zero : IsZero ((Excision.bottomSES Y A).X₁.homology q) :=
    hk.of_iso hhom_iso

  have hf_zero : HomologicalComplex.homologyMap (Excision.bottomSES Y A).f q = 0 :=
    hA_zero.eq_of_src _ _

  exact hexact.isZero_X₂ hf_zero hg_zero

end CWComplex.SkeletonHomology






namespace CWComplex.SkeletonHomology

/-- The preimage of `X_m` under the inclusion `X_{m+1} ↪ X` is homeomorphic to `X_m`. -/
def skeletonPreimageHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≃ₜ
    ↥(CWComplex.skeleton X m : Set X) :=
  { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hx⟩, hx⟩
      left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
      right_inv := fun ⟨x, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val }

/-- The `TopCat`-isomorphism corresponding to `skeletonPreimageHomeo`. -/
def skeletonPreimageIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≅
    TopCat.of ↥(CWComplex.skeleton X m : Set X) :=
  TopCat.isoOfHomeo (skeletonPreimageHomeo m)

/-- For `k ≤ m`, the inclusion of preimages: viewing `X_k` and `X_m` as subsets of `X_{m+1}`,
the inclusion `(X_k \text{ in } X_{m+1}) ↪ (X_m \text{ in } X_{m+1})`. -/
def skeletonPreimageInclusion
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ⟶
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :=
  TopCat.ofHom ⟨fun ⟨y, hy⟩ => ⟨y, Topology.RelCWComplex.skeleton_mono
    (by norm_cast) hy⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- Factorisation of subspace inclusions: the inclusion of the preimage of `X_k` factors
through the preimage of `X_m` whenever `k ≤ m`. -/
lemma subspaceTopInclusion_factor
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    (Excision.subspaceTopInclusion
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X))) =
    skeletonPreimageInclusion k m hkm ≫
      (Excision.subspaceTopInclusion
        (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
          Set ↥(CWComplex.skeleton X (m + 1) : Set X))) := by
  ext ⟨_, _⟩; rfl

/-- Singular-chain version of `subspaceTopInclusion_factor`: the chain-inclusion factors
through the analogous chain-inclusion for the intermediate skeleton. -/
lemma subspaceChainInclusion_factor
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.subspaceChainInclusion
      ↥(CWComplex.skeleton X (m + 1) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) =
    Excision.singularChainZ.map (skeletonPreimageInclusion k m hkm) ≫
      Excision.subspaceChainInclusion
        ↥(CWComplex.skeleton X (m + 1) : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)) := by
  show Excision.singularChainZ.map (Excision.subspaceTopInclusion _) =
    Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
  rw [← Excision.singularChainZ.map_comp, ← subspaceTopInclusion_factor k m hkm]

/-- The preimage-of-a-preimage homeomorphism identifying the nested preimage of `X_k`
inside `X_m ⊆ X_{m+1}` with the direct preimage of `X_k` inside `X_m`. -/
def skeletonPreimageSubHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    ↥(Subtype.val ⁻¹' (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≃ₜ
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  { toEquiv := {
      toFun := fun ⟨⟨⟨x, hxm1⟩, hxm⟩, hxk⟩ => ⟨⟨x, hxm⟩, hxk⟩
      invFun := fun ⟨⟨x, hxm⟩, hxk⟩ => ⟨⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hxm⟩, hxm⟩, hxk⟩
      left_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }

/-- The `TopCat`-iso corresponding to `skeletonPreimageSubHomeo`. -/
def skeletonPreimageSubIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  TopCat.isoOfHomeo (skeletonPreimageSubHomeo k m hkm)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageIso`. -/
def skeletonPreimageChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (m : ℕ) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(CWComplex.skeleton X m : Set X)) :=
  Excision.singularChainZ.mapIso (skeletonPreimageIso m)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageSubIso`. -/
def skeletonPreimageSubChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹'
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)) :
      Set ↥(Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X) :
        Set ↥(CWComplex.skeleton X (m + 1) : Set X)))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X))) :=
  Excision.singularChainZ.mapIso (skeletonPreimageSubIso k m hkm)

/-- The induced isomorphism on singular homology corresponding to `skeletonPreimageIso`. -/
def skeletonPreimageHomologyIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n m : ℕ) :
    (Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹'
      (CWComplex.skeleton X m : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)))).homology n ≅
    SingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (skeletonPreimageChainIso m)

end CWComplex.SkeletonHomology

namespace CWComplex.SkeletonHomology

/-- The homeomorphism between two presentations of `X_k` as a subspace: as the preimage
of `X_k` inside `X_{m+1}` and as the preimage of `X_k` inside `X_m`. -/
def skeletonPreimageAkHomeo
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≃ₜ
    ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  { toEquiv := {
      toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast) hx⟩, hx⟩
      invFun := fun ⟨⟨x, hxm⟩, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
          (by norm_cast; omega) hxm⟩, hx⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }

/-- The `TopCat`-iso corresponding to `skeletonPreimageAkHomeo`. -/
def skeletonPreimageAkIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X)) ≅
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) :=
  TopCat.isoOfHomeo (skeletonPreimageAkHomeo k m hkm)

/-- The induced isomorphism between singular chain complexes corresponding to
`skeletonPreimageAkIso`. -/
def skeletonPreimageAkChainIso
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X (m + 1) : Set X))) ≅
    Excision.singularChainZ.obj (TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X))) :=
  Excision.singularChainZ.mapIso (skeletonPreimageAkIso k m hkm)

/-- Commutativity of the square relating the preimage inclusion to the subspace
chain inclusion through the relevant chain isomorphisms. -/
lemma skeletonPreimageInclusion_comm
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (k m : ℕ) (hkm : k ≤ m) :
    Excision.singularChainZ.map (skeletonPreimageInclusion k m hkm) ≫
      (skeletonPreimageChainIso (X := X) m).hom =
    (skeletonPreimageAkChainIso (X := X) k m hkm).hom ≫
      Excision.subspaceChainInclusion
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) := by
  show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
    Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
  rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp]
  congr 1


set_option maxHeartbeats 1600000 in
/-- The exact sequence of the triple `(X_{m+1}, X_m, X_k)`: there is an exact short
complex relating the three relative homology groups `H_n(X_m, X_k) →
H_n(X_{m+1}, X_k) → H_n(X_{m+1}, X_m)`. -/
theorem triple_exact
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n k m : ℕ) (hkm : k ≤ m) :
    ∃ (S : ShortComplex AddCommGrpCat),
      S.X₁ = Excision.RelativeSingularHomologyGroup n
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ∧
      S.X₂ = Excision.RelativeSingularHomologyGroup n
        ↥(CWComplex.skeleton X (m + 1) : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ∧
      S.X₃ = Excision.RelativeSingularHomologyGroup n
        ↥(CWComplex.skeleton X (m + 1) : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)) ∧
      S.Exact := by

  set Y : Type := ↥(CWComplex.skeleton X (m + 1) : Set X)
  set Ak : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)
  set Am : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X)

  set f := Excision.singularChainZ.map (skeletonPreimageInclusion (X := X) k m hkm)
  set g := Excision.subspaceChainInclusion Y Am

  have hfg : f ≫ g = Excision.subspaceChainInclusion Y Ak :=
    (subspaceChainInclusion_factor (X := X) k m hkm).symm

  haveI hf_mono : Mono f := by
    haveI : Mono (skeletonPreimageInclusion (X := X) k m hkm) := by
      rw [TopCat.mono_iff_injective]
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' : (a : Y) = (b : Y) := by
        have := congr_arg Subtype.val h
        simp only [skeletonPreimageInclusion, TopCat.ofHom] at this
        exact this
      exact Subtype.ext h'
    exact Functor.map_mono _ _
  haveI hg_mono : Mono g := Excision.subspaceChainInclusion_mono Y Am
  haveI hfg_mono : Mono (f ≫ g) := hfg ▸ Excision.subspaceChainInclusion_mono Y Ak

  have hse := Excision.thirdIso_shortExact f g

  have hexact := hse.homology_exact₂ n

  have hcomm := skeletonPreimageInclusion_comm (X := X) k m hkm
  have hcoker_iso : cokernel f ≅
      Excision.relativeSingularChainComplex
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) :=
    cokernel.mapIso f
      (Excision.subspaceChainInclusion
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))
      (skeletonPreimageAkChainIso (X := X) k m hkm)
      (skeletonPreimageChainIso (X := X) m)
      hcomm

  have hhom_iso : (cokernel f).homology n ≅
      Excision.RelativeSingularHomologyGroup n
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso hcoker_iso


  set ses := ShortComplex.mk
      (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
      (by apply (cancel_epi (cokernel.π f)).mp
          simp only [comp_zero, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
            Category.id_comp, cokernel.condition])

  set S := ShortComplex.mk
    (hhom_iso.inv ≫ HomologicalComplex.homologyMap ses.f n)
    (HomologicalComplex.homologyMap ses.g n)
    (by simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp, ses.zero,
            HomologicalComplex.homologyMap_zero, comp_zero])
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  ·
    rfl
  ·
    show (cokernel (f ≫ g)).homology n = _
    rw [hfg]; rfl
  ·
    rfl
  ·
    have e : S ≅ ShortComplex.mk
        (HomologicalComplex.homologyMap ses.f n)
        (HomologicalComplex.homologyMap ses.g n)
        (by rw [← HomologicalComplex.homologyMap_comp, ses.zero,
                HomologicalComplex.homologyMap_zero]) :=
      ShortComplex.isoMk hhom_iso.symm (Iso.refl _) (Iso.refl _)
        (by simp [S]) (by simp [S])
    exact (ShortComplex.exact_iff_of_iso e).mpr hexact
end CWComplex.SkeletonHomology

/-- One inductive step using the triple long exact sequence: if both
`H_n(X_{m+1}, X_m)` and `H_n(X_m, X_k)` vanish, then so does `H_n(X_{m+1}, X_k)`. -/
theorem CWComplex.SkeletonHomology.relativeHomology_triple_step
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n k m : ℕ) (hkm : k ≤ m)
    (h_step : IsZero (Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X (m + 1) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X m : Set X))))
    (h_prev : IsZero (Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))))
    (_h_prev_lo : ∀ (j : ℕ), (ComplexShape.down ℕ).Rel n j →
      IsZero (Excision.RelativeSingularHomologyGroup j
        ↥(CWComplex.skeleton X m : Set X)
        (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)))) :
    IsZero (Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X (m + 1) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))) := by
  obtain ⟨S, hS1, hS2, hS3, hexact⟩ :=
    CWComplex.SkeletonHomology.triple_exact (X := X) n k m hkm
  have hX1_zero : IsZero S.X₁ := hS1 ▸ h_prev
  have hX3_zero : IsZero S.X₃ := hS3 ▸ h_step
  have hf : S.f = 0 := hX1_zero.eq_of_src _ _
  have hg : S.g = 0 := hX3_zero.eq_of_tgt _ _
  have hX2_zero : IsZero S.X₂ := hexact.isZero_X₂ hf hg
  exact hS2 ▸ hX2_zero

/-- The relative homology of a pair with itself, `H_n(X_k, X_k)`, vanishes. -/
theorem CWComplex.SkeletonHomology.relativeHomology_self_isZero
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n k : ℕ) :
    IsZero (Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X k : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X))) := by

  have h_eq : (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X k : Set X)) = Set.univ := by
    ext ⟨_, hx⟩; simp [Set.mem_preimage, hx]
  rw [show Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X k : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) =
    Excision.RelativeSingularHomologyGroup n
      ↥(CWComplex.skeleton X k : Set X) Set.univ from by rw [h_eq]]


  unfold Excision.RelativeSingularHomologyGroup Excision.relativeSingularChainComplex
    Excision.subspaceChainInclusion
  haveI : IsIso (Excision.subspaceTopInclusion (Set.univ :
      Set ↥(CWComplex.skeleton X k : Set X))) := by
    have : Excision.subspaceTopInclusion (Set.univ :
        Set ↥(CWComplex.skeleton X k : Set X)) =
        (TopCat.isoOfHomeo (Homeomorph.Set.univ
          ↥(CWComplex.skeleton X k : Set X))).hom := by
      ext x; simp [Excision.subspaceTopInclusion, TopCat.isoOfHomeo, Homeomorph.Set.univ]
    rw [this]; infer_instance

  haveI : IsIso (Excision.singularChainZ.map (Excision.subspaceTopInclusion (Set.univ :
      Set ↥(CWComplex.skeleton X k : Set X)))) :=
    Excision.singularChainZ.map_isIso _

  exact Functor.map_isZero _ (isZero_cokernel_of_epi _)


/-- The continuous map sending a point of the preimage of `X_k` inside `X_m` to the
corresponding point of `X_k ⊆ X`. -/
def CWComplex.SkeletonHomology.skelPairSubspaceMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) ⟶
    TopCat.of ↥(↑(CWComplex.skeleton X k : Set X) : Set X) :=
  TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the natural square for the pair maps: the subspace inclusion of
`X_k` (as a preimage in `X_m`) into `X_m`, then into `X`, equals the composition through
`X_k ⊆ X`. -/
lemma CWComplex.SkeletonHomology.skelPairSquare_comm
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X) :
      Set ↥(CWComplex.skeleton X m : Set X)) ≫
    CWComplex.SkeletonHomology.skeletonInclusion X m =
    CWComplex.SkeletonHomology.skelPairSubspaceMap k m ≫
    Excision.subspaceTopInclusion (↑(CWComplex.skeleton X k : Set X) : Set X) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The induced map of relative singular chain complexes from the pair `(X_m, X_k)`
to the pair `(X, X_k)`. -/
noncomputable def CWComplex.SkeletonHomology.skelPairRelativeChainMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (k m : ℕ) :
    Excision.relativeSingularChainComplex ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ⟶
    Excision.relativeSingularChainComplex X
      (↑(CWComplex.skeleton X k : Set X)) :=
  cokernel.map _ _
    (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skelPairSubspaceMap k m))
    (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonInclusion X m))
    (by
      show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
        Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
      rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp,
        CWComplex.SkeletonHomology.skelPairSquare_comm])

/-- The induced map on relative singular homology
`H_n(X_m, X_k) → H_n(X, X_k)`. -/
noncomputable def CWComplex.SkeletonHomology.skelPairHomologyMap
    {X : Type} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n k m : ℕ) :
    Excision.RelativeSingularHomologyGroup n ↥(CWComplex.skeleton X m : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X k : Set X)) ⟶
    Excision.RelativeSingularHomologyGroup n X
      (↑(CWComplex.skeleton X k : Set X)) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (CWComplex.SkeletonHomology.skelPairRelativeChainMap k m)








namespace CWComplex.SkeletonHomology


end CWComplex.SkeletonHomology

namespace CWHomology

/-- The cellular chain group `C_n(X)` packaged as an object of the category `AddCommGrpCat`. -/
noncomputable def cellularChainObj (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (CWComplex.cellularChains X n)

open Excision in
/-- The relative singular homology `H_q(X_n, X_{n-1})` of the CW pair, packaged as an
object of `AddCommGrpCat`. -/
noncomputable def relHomologySkeleton (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n q : ℕ) : AddCommGrpCat :=
  RelativeSingularHomologyGroup q
    (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))
    (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X))

/-- The singular homology `H_q(X_n)` of the `n`-skeleton, packaged as an object of
`AddCommGrpCat`. -/
noncomputable def skeletonHomology (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n q : ℕ) : AddCommGrpCat :=
  SingularHomologyGroup q (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))







/-- The connecting homomorphism `H_{n+1}(X_{n+1}, X_n) → H_n(X_n)` arising from the
short exact sequence of the pair `(X_{n+1}, X_n)`. -/
noncomputable def skeletonConnectingHom (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    relHomologySkeleton X (n + 1) (n + 1) ⟶ skeletonHomology X n n := by

  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)

  let hse := Excision.bottomSES_shortExact Y A
  let hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

  let delta := hse.δ (n + 1) n hRel

  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
        toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
            (by norm_cast; omega) hx⟩, hx⟩
        left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
        right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo

  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)

  exact delta ≫ hhom_iso.hom


/-- The map `H_n(X_n) → H_n(X_n, X_{n-1})` induced by the quotient of chain complexes. -/
noncomputable def skeletonInclusionMap (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonHomology X n n ⟶ relHomologySkeleton X n n :=


  HomologicalComplex.homologyMap
    (Excision.bottomSES
      (↥(CWComplex.skeleton X (n : ℕ∞) : Set X))
      (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X))).g n



/-- The composition `H_{n+1}(X_{n+1}) → H_{n+1}(X_{n+1}, X_n) → H_n(X_n)` vanishes by
exactness of the long exact sequence of the pair. -/
theorem skeletonInclusionMap_comp_skeletonConnectingHom
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonInclusionMap X (n + 1) ≫ skeletonConnectingHom X n = 0 := by

  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)

  have hse := Excision.bottomSES_shortExact Y A
  have hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

  let delta := hse.δ (n + 1) n hRel

  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
        toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
            (by norm_cast; omega) hx⟩, hx⟩
        left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
        right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo

  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)


  have hincl : skeletonInclusionMap X (n + 1) =
      HomologicalComplex.homologyMap (Excision.bottomSES Y A).g (n + 1) := rfl

  have hconn : skeletonConnectingHom X n = delta ≫ hhom_iso.hom := rfl
  rw [hincl, hconn]

  have h_comp_delta := hse.comp_δ (n + 1) n hRel

  change HomologicalComplex.homologyMap (Excision.bottomSES Y A).g (n + 1) ≫
    hse.δ (n + 1) n hRel ≫ hhom_iso.hom = 0
  rw [reassoc_of% h_comp_delta]
  exact zero_comp





/-- The inclusion-induced map `H_n(X_n) → H_n(X_{n+1})`. -/
noncomputable def skeletonStepMap (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonHomology X n n ⟶ skeletonHomology X (n + 1) n :=
  CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n


/-- The composition `H_{n+1}(X_{n+1}, X_n) → H_n(X_n) → H_n(X_{n+1})` vanishes by
exactness of the long exact sequence of the pair. -/
theorem skeletonConnectingHom_comp_skeletonStepMap
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonConnectingHom X n ≫ skeletonStepMap X n = 0 := by

  let Y : Type := ↥(CWComplex.skeleton X (n + 1) : Set X)
  let A : Set Y := Subtype.val ⁻¹' (CWComplex.skeleton X n : Set X)

  have hse := Excision.bottomSES_shortExact Y A
  have hRel : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

  let delta := hse.δ (n + 1) n hRel

  let hA_homeo : ↥A ≃ₜ ↥(CWComplex.skeleton X n : Set X) :=
    { toEquiv := {
        toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
        invFun := fun ⟨x, hx⟩ => ⟨⟨x, Topology.RelCWComplex.skeleton_mono
            (by norm_cast; omega) hx⟩, hx⟩
        left_inv := fun ⟨⟨x, _⟩, _⟩ => rfl
        right_inv := fun ⟨x, _⟩ => rfl }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let hA_iso : TopCat.of ↥A ≅ TopCat.of ↥(CWComplex.skeleton X n : Set X) :=
    TopCat.isoOfHomeo hA_homeo

  let hhom_iso :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (Excision.singularChainZ.mapIso hA_iso)

  have hconn : skeletonConnectingHom X n = delta ≫ hhom_iso.hom := rfl


  have htop_eq : Excision.subspaceTopInclusion A =
      hA_iso.hom ≫ CWComplex.SkeletonHomology.skeletonStepInclusion X n := by
    ext ⟨⟨x, hx_k1⟩, hx_k⟩
    simp only [CategoryTheory.comp_apply]
    rfl
  have hchain_eq : (Excision.bottomSES Y A).f =
      Excision.singularChainZ.map hA_iso.hom ≫
      Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonStepInclusion X n) := by
    show Excision.subspaceChainInclusion Y A = _
    show Excision.singularChainZ.map (Excision.subspaceTopInclusion A) = _
    rw [htop_eq, Excision.singularChainZ.map_comp]
  have hhom_eq : HomologicalComplex.homologyMap (Excision.bottomSES Y A).f n =
      hhom_iso.hom ≫ CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n := by
    show (HomologicalComplex.homologyFunctor _ _ n).map ((Excision.bottomSES Y A).f) =
      (HomologicalComplex.homologyFunctor _ _ n).map (Excision.singularChainZ.map hA_iso.hom) ≫
      (HomologicalComplex.homologyFunctor _ _ n).map
        (Excision.singularChainZ.map (CWComplex.SkeletonHomology.skeletonStepInclusion X n))
    rw [hchain_eq]
    exact (HomologicalComplex.homologyFunctor _ _ n).map_comp _ _

  have hstep : skeletonStepMap X n = CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n := rfl
  rw [hconn, hstep]

  have h_delta_comp := hse.δ_comp (n + 1) n hRel


  rw [hhom_eq] at h_delta_comp

  change (hse.δ (n + 1) n hRel ≫ hhom_iso.hom) ≫
    CWComplex.SkeletonHomology.skeletonStepHomologyMap X n n = 0
  rw [Category.assoc]
  exact h_delta_comp




















/-- A continuous map `f : X → Y` between CW complexes is *cellular* if it sends the
`n`-skeleton of `X` into the `n`-skeleton of `Y` for every `n`. -/
structure IsCellularMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) : Prop where
  mapsTo_skeleton : ∀ (n : ℕ),
    Set.MapsTo f (CWComplex.skeleton X n :) (CWComplex.skeleton Y n :)

/-- The restriction of a cellular map `f : X → Y` to the `n`-skeletons, viewed as a
morphism `X_n ⟶ Y_n` in `TopCat`. -/
def cellularMapOnSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(CWComplex.skeleton X (n : ℕ∞) : Set X) ⟶
    TopCat.of ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨f x, hf.mapsTo_skeleton n hx⟩,
    Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _⟩

/-- The restriction of a cellular map `f` to the previous-skeleton subspace, viewed as a
morphism between the preimages of `X_{n-1}` (in `X_n`) and `Y_{n-1}` (in `Y_n`). -/
def cellularMapOnPrevSkeleton
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ⟶
    TopCat.of ↥(Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) :=
  TopCat.ofHom ⟨fun ⟨⟨x, hxn⟩, hxprev⟩ =>
    ⟨⟨f x, hf.mapsTo_skeleton n hxn⟩, hf.mapsTo_skeleton (n - 1) hxprev⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- The naturality square between the inclusion of the previous-skeleton subspace into
the `n`-skeleton, and the cellular map restricted to skeletons, commutes. -/
lemma cellularMapSquare_comm
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X) :
      Set ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)) ≫
    cellularMapOnSkeleton f hf n =
    cellularMapOnPrevSkeleton f hf n ≫
    Excision.subspaceTopInclusion (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y) :
      Set ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)) := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The induced map between relative singular chain complexes of the CW pairs
`(X_n, X_{n-1})` and `(Y_n, Y_{n-1})` arising from a cellular map. -/
def cellularRelativeChainMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton X (n : ℕ∞) : Set X)
      (Subtype.val ⁻¹' (CWComplex.skeleton X ((↑(n - 1) : ℕ∞)) : Set X)) ⟶
    Excision.relativeSingularChainComplex
      ↥(CWComplex.skeleton Y (n : ℕ∞) : Set Y)
      (Subtype.val ⁻¹' (CWComplex.skeleton Y ((↑(n - 1) : ℕ∞)) : Set Y)) :=
  cokernel.map _ _
    (Excision.singularChainZ.map (cellularMapOnPrevSkeleton f hf n))
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n))
    (by
      show Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _ =
        Excision.singularChainZ.map _ ≫ Excision.singularChainZ.map _
      rw [← Excision.singularChainZ.map_comp, ← Excision.singularChainZ.map_comp,
        cellularMapSquare_comm])

/-- The induced map on relative singular homology
`H_n(X_n, X_{n-1}) → H_n(Y_n, Y_{n-1})` arising from a cellular map. -/
def relHomologySkeletonMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    relHomologySkeleton X n n ⟶ relHomologySkeleton Y n n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (cellularRelativeChainMap f hf n)


/-- The induced map on absolute singular homology of the skeletons,
`H_n(X_n) → H_n(Y_n)`, arising from a cellular map. -/
def skeletonAbsHomologyMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) (n : ℕ) :
    skeletonHomology X n n ⟶ skeletonHomology Y n n :=
  HomologicalComplex.homologyMap
    (Excision.singularChainZ.map (cellularMapOnSkeleton f hf n)) n






/-- The map on singular homology `H_n(X) → H_n(Y)` induced by a continuous map. -/
noncomputable def singularHomologyMap (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SingularHomologyGroup n X ⟶ SingularHomologyGroup n Y :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)


/-- The induced map `H_n(X_{n+1}) → H_n(Y_{n+1})` from the restriction of a cellular
map to `(n+1)`-skeletons. -/
noncomputable def skeletonHomologyMapInduced (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) :
    skeletonHomology X (n + 1) n ⟶ skeletonHomology Y (n + 1) n :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
    (cellularMapOnSkeleton f hf (n + 1))

/-- Topological commutativity of the square: inclusion of the `(n+1)`-skeleton followed
by `f` equals the restriction of `f` to skeletons followed by inclusion into `Y`. -/
lemma skeletonInclusion_cellularMap_comm (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) :
    CWComplex.SkeletonHomology.skeletonInclusion X (n + 1) ≫ TopCat.ofHom f =
    cellularMapOnSkeleton f hf (n + 1) ≫ CWComplex.SkeletonHomology.skeletonInclusion Y (n + 1) := by
  ext ⟨x, hx⟩; rfl

/-- Naturality of the `H_n(X_{n+1}) → H_n(X)` map with respect to cellular maps. -/
lemma skeletonHomologyMap_naturality (n : ℕ)
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) (hf : IsCellularMap f) :
    skeletonHomologyMapInduced n f hf ≫
      CWComplex.SkeletonHomology.skeletonHomologyMap Y n (n + 1) =
    CWComplex.SkeletonHomology.skeletonHomologyMap X n (n + 1) ≫ singularHomologyMap n f := by
  show ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (cellularMapOnSkeleton f hf (n + 1)) ≫
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (CWComplex.SkeletonHomology.skeletonInclusion Y (n + 1)) =
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map
      (CWComplex.SkeletonHomology.skeletonInclusion X (n + 1)) ≫
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
  rw [← Functor.map_comp, ← Functor.map_comp,
    skeletonInclusion_cellularMap_comm]




end CWHomology

namespace CellularHomology

open Topology

/-- A CW complex has *only even cells* if there are no cells of odd dimension. -/
def HasOnlyEvenCells (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∀ k : ℕ, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) (2 * k + 1))

/-- If `X` has only even cells, the cellular chain group `C_{2k+1}(X)` in odd degree is
trivial (a subsingleton). -/
theorem cellularChains_odd_subsingleton (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (heven : HasOnlyEvenCells X) (k : ℕ) :
    Subsingleton (CWComplex.cellularChains X (2 * k + 1)) := by
  haveI := heven k
  infer_instance



end CellularHomology
