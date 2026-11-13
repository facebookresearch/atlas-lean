/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace GaloisTheory

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem card_aut_le_finrank (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nat.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
  rw [Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

theorem isGalois_iff_card_aut_eq_finrank (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois F E ↔ Nat.card (E ≃ₐ[F] E) = Module.finrank F E :=
  ⟨fun _ => IsGalois.card_aut_eq_finrank F E,
   fun h => IsGalois.of_card_aut_eq_finrank F E h⟩

theorem galois_group_size (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    (Nat.card (E ≃ₐ[F] E) ≤ Module.finrank F E) ∧
    (IsGalois F E ↔ Nat.card (E ≃ₐ[F] E) = Module.finrank F E) :=
  ⟨card_aut_le_finrank F E, isGalois_iff_card_aut_eq_finrank F E⟩

noncomputable def fundamentalTheoremSymmetricPolynomials
    (σ : Type*) (R : Type*) {n : ℕ} [Fintype σ] [CommRing R]
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] ↥(MvPolynomial.symmetricSubalgebra σ R) :=
  MvPolynomial.esymmAlgEquiv σ R hn

set_option maxHeartbeats 400000 in
open Polynomial MvPolynomial Finset in
theorem symmetric_polynomial_in_esymm
    {F : Type*} [Field F] {P : Polynomial F} (hP : P.Monic) (hsplit : P.Splits)
    (n : ℕ) (hn : P.natDegree = n)
    (f : MvPolynomial (Fin n) F) (hf : f.IsSymmetric)
    (α : Fin n → F) (hα : P = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) :
    ∃ q : MvPolynomial (Fin n) F,
      MvPolynomial.eval α f =
        MvPolynomial.eval (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) q := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  set q := (MvPolynomial.esymmAlgEquiv (Fin n) F hcard).symm ⟨f, hf⟩
  refine ⟨q, ?_⟩
  have hfq : f = (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))) q := by
    have h1 : ((MvPolynomial.esymmAlgEquiv (Fin n) F hcard) q).val = f := by
      simp [q, AlgEquiv.apply_symm_apply]
    rw [← h1]
    change ((MvPolynomial.esymmAlgHom (Fin n) F n) q).val = _
    exact MvPolynomial.esymmAlgHom_apply (σ := Fin n) q
  suffices h : ∀ i : Fin n,
      MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
        (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1)) by
    rw [hfq]
    have key : (MvPolynomial.eval α).comp (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))).toRingHom =
        MvPolynomial.eval
          (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [MvPolynomial.eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.aeval_X, MvPolynomial.eval_X]
        exact h i
    exact RingHom.congr_fun key q
  intro i
  have hesymm : MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
      (Finset.univ.val.map α).esymm (i.val + 1) := by
    have := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) F (i.val + 1) α
    rwa [MvPolynomial.aeval_def] at this
  rw [hesymm]
  have hroots : P.roots = Finset.univ.val.map α := by
    rw [hα, Finset.prod_eq_multiset_prod]
    conv_lhs =>
      rw [show Multiset.map (fun i => Polynomial.X - Polynomial.C (α i)) Finset.univ.val =
        Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Finset.univ.val.map α) from by
          rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [← hroots]
  have hi_le : n - (i.val + 1) ≤ P.natDegree := by omega
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hi_le
  rw [hP.leadingCoeff, one_mul] at hvieta
  have hsub : P.natDegree - (n - (i.val + 1)) = i.val + 1 := by omega
  rw [hsub] at hvieta
  rw [hvieta, ← mul_assoc, ← pow_add]
  simp

theorem all_minpoly_split_in_splitting_field {F : Type*} [Field F]
    (p : Polynomial F) (α : p.SplittingField) :
    (Polynomial.map (algebraMap F p.SplittingField) (minpoly F α)).Splits := by
  haveI : Normal F p.SplittingField := Polynomial.SplittingField.instNormal p
  exact Normal.splits inferInstance α

abbrev IsSolvableGroup (G : Type*) [Group G] : Prop := IsSolvable G

theorem s5_not_solvable_and_a5_simple :
    ¬IsSolvable (Equiv.Perm (Fin 5)) ∧ IsSimpleGroup (alternatingGroup (Fin 5)) :=
  ⟨Equiv.Perm.fin_5_not_solvable, alternatingGroup.isSimpleGroup_five⟩

theorem symmetric_group_not_solvable {n : ℕ} (hn : 5 ≤ n) :
    ¬IsSolvable (Equiv.Perm (Fin n)) := by
  apply Equiv.Perm.not_solvable
  rw [Cardinal.mk_fin]
  exact_mod_cast hn

open Polynomial in
theorem not_solvableByRad_of_gal_iso_S5 {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : F[X]} (hp : Irreducible p)
    (hiso : p.Gal ≃* Equiv.Perm (Fin 5))
    {x : E} (hpx : aeval x p = 0) :
    x ∉ solvableByRad F E := by
  intro hx
  have hsol : IsSolvable p.Gal := isSolvable_gal_of_irreducible hx hp hpx
  have : IsSolvable (Equiv.Perm (Fin 5)) := by
    haveI := hsol
    exact solvable_of_surjective (f := hiso.toMonoidHom) hiso.surjective
  exact Equiv.Perm.fin_5_not_solvable this
