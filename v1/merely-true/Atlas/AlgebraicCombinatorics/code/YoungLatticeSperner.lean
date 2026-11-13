/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn
import Atlas.AlgebraicCombinatorics.code.GroupActions

set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn
open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

def wreathElemToPerm (g : WreathElem m n) : Equiv.Perm (Fin m × Fin n) :=
  Equiv.ofBijective g.actOn g.actOn_injective.bijective_of_finite

noncomputable def wreathSubgroup (m n : ℕ) : Subgroup (Equiv.Perm (Fin (m * n))) :=
  Subgroup.closure
    {π | ∃ g : WreathElem m n,
      π = finProdFinEquiv.permCongr (wreathElemToPerm g)}

lemma wreathElemToPerm_apply (g : WreathElem m n) (p : Fin m × Fin n) :
    wreathElemToPerm g p = g.actOn p := rfl

lemma sum_rowSize_eq_card (S : Finset (Fin m × Fin n)) :
    ∑ i : Fin m, rowSize S i = S.card := by
  simp only [rowSize]
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => S.filter (fun p => p.1 = i)) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_filter]
    intro ⟨_, _⟩ _ ha hj
    exact hij (ha ▸ hj)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
  constructor
  · rintro ⟨_, h1, _⟩; exact h1
  · intro h; exact ⟨i, h, rfl⟩

lemma image_finProdFinEquiv_actOnSet (g : WreathElem m n)
    (S : Finset (Fin m × Fin n)) :
    (g.actOnSet S).image finProdFinEquiv =
    (finProdFinEquiv.permCongr (wreathElemToPerm g)) •
      (S.image finProdFinEquiv) := by
  simp only [Finset.smul_finset_def, WreathElem.actOnSet, Equiv.Perm.smul_def]
  rw [Finset.image_image, Finset.image_image]
  congr 1; funext x
  simp only [Function.comp, Equiv.permCongr_apply, wreathElemToPerm_apply,
    Equiv.symm_apply_apply]

lemma smul_image_symm_eq_actOnSet (g : WreathElem m n)
    (A : Finset (Fin (m * n))) :
    ((finProdFinEquiv.permCongr (wreathElemToPerm g)) • A).image
      finProdFinEquiv.symm =
    g.actOnSet (A.image finProdFinEquiv.symm) := by
  simp only [Finset.smul_finset_def, WreathElem.actOnSet, Equiv.Perm.smul_def]
  rw [Finset.image_image, Finset.image_image]
  congr 1; funext x
  simp only [Function.comp, Equiv.permCongr_apply, wreathElemToPerm_apply,
    Equiv.symm_apply_apply]

lemma wreathSubgroup_orbit_of_sameOrbit (S T : Finset (Fin m × Fin n))
    (h : WreathOrbits.SameOrbit S T) :
    ∃ (g : ↥(wreathSubgroup m n)),
      g • (S.image finProdFinEquiv) = T.image finProdFinEquiv := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨⟨_, Subgroup.subset_closure ⟨w, rfl⟩⟩,
    (image_finProdFinEquiv_actOnSet w S).symm⟩

set_option maxHeartbeats 1600000 in
lemma sameOrbit_of_wreathSubgroup_orbit
    (A : Finset (Fin (m * n)))
    (g : ↥(wreathSubgroup m n)) :
    WreathOrbits.SameOrbit (A.image finProdFinEquiv.symm)
      ((g • A).image finProdFinEquiv.symm) := by
  suffices key : ∀ (π : Equiv.Perm (Fin (m * n))) (_ : π ∈ wreathSubgroup m n)
      (C : Finset (Fin (m * n))),
      rowSizeMultiset ((π • C).image finProdFinEquiv.symm) =
        rowSizeMultiset (C.image finProdFinEquiv.symm) by
    exact (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr (key g.1 g.2 A).symm
  intro π hπ
  induction hπ using Subgroup.closure_induction with
  | mem x hx =>
    intro C
    obtain ⟨w, rfl⟩ := hx
    rw [smul_image_symm_eq_actOnSet]
    exact ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp ⟨w, rfl⟩).symm
  | one => intro C; simp only [one_smul]
  | mul x y _ _ ihx ihy =>
    intro C; rw [mul_smul, ihx (y • C), ihy C]
  | inv x _ ih =>
    intro C
    specialize ih (x⁻¹ • C)
    rw [smul_inv_smul] at ih
    exact ih.symm

set_option maxHeartbeats 1600000 in
noncomputable def quotientPosetEquivWreathQuotient (m n : ℕ) :
    QuotientPoset (m * n) (wreathSubgroup m n) ≃ WreathQuotient m n where
  toFun := Quotient.lift
    (fun (A : Finset (Fin (m * n))) => wreathQuotientMk (A.image finProdFinEquiv.symm))
    (fun (A B : Finset (Fin (m * n))) (hab : _) => by
      rw [wreathQuotientMk_eq_iff]
      obtain ⟨g, rfl⟩ := hab
      exact (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
        ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp
          (sameOrbit_of_wreathSubgroup_orbit B g)).symm)
  invFun := Quotient.lift
    (fun (S : Finset (Fin m × Fin n)) => @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
      (S.image finProdFinEquiv))
    (fun (S T : Finset (Fin m × Fin n)) (hST : _) => by
      apply Quotient.sound
      obtain ⟨g, hg⟩ := wreathSubgroup_orbit_of_sameOrbit T S
        ((sameOrbit_iff_rowSizeMultiset_eq T S).mpr
          ((sameOrbit_iff_rowSizeMultiset_eq S T).mp hST).symm)
      exact ⟨g, hg⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ A =>
      simp only [Quotient.lift_mk, wreathQuotientMk]
      congr 1; rw [Finset.image_image]; simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ S =>
      simp only [Quotient.lift_mk, wreathQuotientMk]
      congr 1; rw [Finset.image_image]; simp

set_option maxHeartbeats 1600000 in
noncomputable def quotientPosetIsoWreathQuotient (m n : ℕ) :
    QuotientPoset (m * n) (wreathSubgroup m n) ≃o WreathQuotient m n where
  toEquiv := quotientPosetEquivWreathQuotient m n
  map_rel_iff' := by
    intro a b
    let f := quotientPosetEquivWreathQuotient m n
    constructor
    · rintro ⟨S, T, hS, hT, hsub⟩
      have ha : a = @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
          (S.image finProdFinEquiv) := by
        rw [← f.symm_apply_apply a, ← hS]
        show f.symm (wreathQuotientMk S) = _
        simp only [f, quotientPosetEquivWreathQuotient, Equiv.coe_fn_symm_mk,
          wreathQuotientMk, Quotient.lift_mk]
      have hb : b = @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
          (T.image finProdFinEquiv) := by
        rw [← f.symm_apply_apply b, ← hT]
        show f.symm (wreathQuotientMk T) = _
        simp only [f, quotientPosetEquivWreathQuotient, Equiv.coe_fn_symm_mk,
          wreathQuotientMk, Quotient.lift_mk]
      exact ⟨S.image finProdFinEquiv, T.image finProdFinEquiv, ha.symm, hb.symm,
        Finset.image_subset_image hsub⟩
    · rintro ⟨S, T, hS, hT, hsub⟩
      refine ⟨S.image finProdFinEquiv.symm, T.image finProdFinEquiv.symm, ?_, ?_,
        Finset.image_subset_image hsub⟩
      · subst hS; rfl
      · subst hT; rfl

lemma sumParts_gridYoungToLmn (S : GridYoungDiagram m n) :
    sumParts (gridYoungToLmn S) = S.val.card := by
  simp only [sumParts, gridYoungToLmn]
  exact sum_rowSize_eq_card S.val

lemma grade_composed_iso (A : Finset (Fin (m * n))) :
    letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
    grade ℕ ((wreathQuotientIsoLmn m n)
      (wreathQuotientMk (A.image finProdFinEquiv.symm))) =
    A.card := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  rw [grade_eq]
  show sumParts ((wreathQuotientIsoLmn m n) (wreathQuotientMk (A.image finProdFinEquiv.symm))) =
    A.card
  let S := A.image finProdFinEquiv.symm
  have hunfold : (wreathQuotientIsoLmn m n) (wreathQuotientMk S) =
      gridYoungToLmn ⟨canonicalYoung S, canonicalYoung_isGridYoung S⟩ := by
    simp [wreathQuotientIsoLmn, wreathQuotientIsoGridYoung, wreathQuotientToGridYoung,
      quotientIsoLmn, wreathQuotientMk]
  rw [hunfold, sumParts_gridYoungToLmn]
  have hco : SameOrbit (canonicalYoung S) S :=
    (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
      ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp (canonicalYoung_sameOrbit S)).symm
  rw [card_eq_of_sameOrbit hco]
  exact Finset.card_image_of_injective A finProdFinEquiv.symm.injective

set_option maxHeartbeats 1600000 in
def quotientPosetIsoLmn (m n : ℕ) :
    letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
    letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
    { e : QuotientPoset (m * n) (wreathSubgroup m n) ≃o Lmn m n //
      ∀ p, grade ℕ (e p) = grade ℕ p } := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  let e := (quotientPosetIsoWreathQuotient m n).trans (wreathQuotientIsoLmn m n)
  refine ⟨e, fun p => ?_⟩
  induction p using Quotient.inductionOn with
  | _ A =>
    have lhs_eq : grade ℕ (e (@Quotient.mk _ (orbitRel _ _) A)) = A.card := by
      show grade ℕ ((wreathQuotientIsoLmn m n)
        ((quotientPosetIsoWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A))) = A.card
      have hbridge : (quotientPosetIsoWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A) =
          wreathQuotientMk (A.image finProdFinEquiv.symm) := by
        show (quotientPosetEquivWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A) = _
        simp [quotientPosetEquivWreathQuotient]
      rw [hbridge]
      exact grade_composed_iso A
    have rhs_eq : grade ℕ (@Quotient.mk _ (orbitRel (wreathSubgroup m n)
        (Finset (Fin (m * n)))) A) = A.card := rfl
    rw [lhs_eq, rhs_eq]

theorem hasSpernerProperty (m n : ℕ) : HasSpernerProperty (α := Lmn m n) := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  obtain ⟨e, hgrade⟩ := quotientPosetIsoLmn m n
  exact hasSpernerProperty_of_orderIso e hgrade boolean_quotient_sperner

theorem Lmn_isRankUnimodal (m n : ℕ) : IsRankUnimodal (α := Lmn m n) := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  obtain ⟨e, hgrade⟩ := quotientPosetIsoLmn m n
  exact isRankUnimodal_of_orderIso e hgrade boolean_quotient_unimodal

theorem isRankSymmetric_and_isRankUnimodal_and_hasSpernerProperty (m n : ℕ) :
    IsRankSymmetric (α := Lmn m n) ∧
    IsRankUnimodal (α := Lmn m n) ∧
    HasSpernerProperty (α := Lmn m n) :=
  ⟨Lmn_isRankSymmetric m n, Lmn_isRankUnimodal m n, hasSpernerProperty m n⟩

end YoungLattice.Lmn
