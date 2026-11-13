/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.HenselLemmas
import Atlas.NumberTheoryI.code.HenselFactorization
import Atlas.NumberTheoryI.code.LocalExtensions
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.LocalRing.Quotient

noncomputable section

open Polynomial IsLocalRing

section HenselRoots

variable {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]

omit [HenselianLocalRing A] in
lemma aeval_eq_eval_residue (p : (ResidueField A)[X]) (x : ResidueField A) :
    aeval x p = eval x p := by
  simp [aeval_def]

theorem hensel_root_lift {f : A[X]} (hf : f.Monic)
    (hsep : (f.map (residue A)).Separable)
    {a₀ : ResidueField A} (ha₀ : (f.map (residue A)).IsRoot a₀) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  have hensel := ((HenselianLocalRing.TFAE (R := A)).out 0 1).mp ‹HenselianLocalRing A›
  have h1 : aeval a₀ f = 0 := by
    have : aeval a₀ f = eval a₀ (map (residue A) f) := by
      simp [aeval_def, eval_map, ResidueField.algebraMap_eq]
    rw [this]; exact ha₀
  have h2 : aeval a₀ (derivative f) ≠ 0 := by
    have key : aeval a₀ (derivative f) = eval a₀ (derivative (map (residue A) f)) := by
      show eval₂ (algebraMap A _) a₀ (derivative f) = _
      rw [ResidueField.algebraMap_eq]
      conv_rhs => rw [Polynomial.derivative_map]
      rw [eval_map]
    rw [key]
    have hroot : aeval a₀ (map (residue A) f) = 0 := by
      rw [aeval_eq_eval_residue]; exact ha₀
    have := hsep.aeval_derivative_ne_zero hroot
    rwa [aeval_eq_eval_residue] at this
  exact hensel f hf a₀ h1 h2

omit [HenselianLocalRing A] in
theorem root_maps_to_residue_root {f : A[X]} {a : A} (ha : f.IsRoot a) :
    (f.map (residue A)).IsRoot (residue A a) := by
  simp only [IsRoot, eval_map]
  rw [eval₂_at_apply, ha, map_zero]

omit [HenselianLocalRing A] in
theorem hensel_root_injective {f : A[X]} (hf : f.Monic)
    (hsep : (f.map (residue A)).Separable)
    {a b : A} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hab : residue A a = residue A b) : a = b := by

  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha

  have hfb : (b - a) * q.eval b = 0 := by
    have := hb; rw [IsRoot, hq, eval_mul, eval_sub, eval_X, eval_C] at this; exact this

  have hqa : f.derivative.eval a = q.eval a := by
    have hd : f.derivative = (X - C a) * q.derivative + q := by
      rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]; ring
    rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add]

  have hderiv : IsUnit (f.derivative.eval a) := by
    rw [← notMem_maximalIdeal]
    intro hmem_deriv
    have h1 : (residue A) (f.derivative.eval a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem_deriv
    have h2 : (residue A) (f.derivative.eval a) =
        eval (residue A a) (derivative (map (residue A) f)) := by
      rw [show (residue A) (f.derivative.eval a) =
        (f.derivative.map (residue A)).eval (residue A a) from by rw [eval_map, eval₂_at_apply]]
      rw [Polynomial.derivative_map]
    rw [h2] at h1
    have hroot : aeval (residue A a) (map (residue A) f) = 0 := by
      rw [aeval_eq_eval_residue]; exact root_maps_to_residue_root ha
    have := hsep.aeval_derivative_ne_zero hroot
    rw [aeval_eq_eval_residue] at this
    exact this h1

  have hqa_unit : IsUnit (q.eval a) := hqa ▸ hderiv

  have hres_q : residue A (q.eval a) = residue A (q.eval b) := by
    rw [show residue A (q.eval a) = (q.map (residue A)).eval (residue A a) from by
      rw [eval_map, eval₂_at_apply]]
    rw [show residue A (q.eval b) = (q.map (residue A)).eval (residue A b) from by
      rw [eval_map, eval₂_at_apply]]
    rw [hab]

  have hqb_unit : IsUnit (q.eval b) := by
    rw [← notMem_maximalIdeal]
    intro hmem_qb
    have h1 : residue A (q.eval b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem_qb
    rw [← hres_q] at h1
    exact (hqa_unit.map (residue A)).ne_zero h1

  have hab_zero : b - a = 0 := by rwa [hqb_unit.mul_left_eq_zero] at hfb
  exact (eq_of_sub_eq_zero hab_zero).symm

end HenselRoots

section HenselRootBijection

variable {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]

end HenselRootBijection

lemma dvr_ker_algebraMap_absurd
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B]
    (h_le : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A B)) : False := by
  have hDVR_B : IsDiscreteValuationRing B := inferInstance
  have h_lift : ∀ a ∈ IsLocalRing.maximalIdeal A, (algebraMap A B) a = 0 :=
    fun a ha => h_le ha
  let f : IsLocalRing.ResidueField A →+* B :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A B) h_lift
  letI algkB : Algebra (IsLocalRing.ResidueField A) B := f.toAlgebra
  have hf_comp : ∀ a : A,
      f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = algebraMap A B a :=
    fun a => Ideal.Quotient.lift_mk _ _ _
  have hintegral : Algebra.IsIntegral (IsLocalRing.ResidueField A) B := by
    constructor; intro b
    obtain ⟨p, hp_monic, hp_eval⟩ := (Algebra.IsIntegral.of_finite A B).isIntegral b
    refine ⟨p.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)), hp_monic.map _, ?_⟩
    show Polynomial.eval₂ f b
      (p.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) = 0
    rw [Polynomial.eval₂_map]
    have : f.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = algebraMap A B := by
      ext a; exact hf_comp a
    rw [this]; exact hp_eval
  exact hDVR_B.not_isField B
    (@isField_of_isIntegral_of_isField' (IsLocalRing.ResidueField A) B _ _ _ algkB hintegral
      (Field.toIsField (IsLocalRing.ResidueField A)))

section ResidueFieldFunctor

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]

omit [HenselianLocalRing A] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁] in
lemma algHom_dvr_isLocalHom (φ : B₁ →ₐ[A] B₂) : IsLocalHom φ.toRingHom := by

  apply ((local_hom_TFAE φ.toRingHom).out 3 0).mp

  have hP_prime : ((maximalIdeal B₂).comap φ.toRingHom).IsPrime :=
    Ideal.comap_isPrime φ.toRingHom (maximalIdeal B₂)

  have hP_contains : ∀ a ∈ maximalIdeal A,
      algebraMap A B₁ a ∈ (maximalIdeal B₂).comap φ.toRingHom := by
    intro a ha
    show φ.toRingHom (algebraMap A B₁ a) ∈ maximalIdeal B₂
    rw [show φ.toRingHom (algebraMap A B₁ a) = algebraMap A B₂ a from φ.commutes a]
    exact map_nonunit (algebraMap A B₂) a ha


  have hP_ne_bot : (maximalIdeal B₂).comap φ.toRingHom ≠ ⊥ := by
    intro hP_bot
    have : maximalIdeal A ≤ RingHom.ker (algebraMap A B₂) := by
      intro a ha
      have h1 := hP_contains a ha
      rw [hP_bot] at h1
      simp only [Ideal.mem_bot] at h1
      show algebraMap A B₂ a = 0
      rw [← φ.commutes a, h1, map_zero]
    exact dvr_ker_algebraMap_absurd A B₂ this

  have hP_max : ((maximalIdeal B₂).comap φ.toRingHom).IsMaximal :=
    @IsPrime.to_maximal_ideal B₁ _ _ _ _ hP_prime hP_ne_bot

  exact (IsLocalRing.eq_maximalIdeal hP_max) ▸ le_refl _

end ResidueFieldFunctor

theorem adjoinRoot_isLocalRing_of_irred_map
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) (hg_monic : g.Monic) [IsDomain (AdjoinRoot g)]
    [Module.Finite A (AdjoinRoot g)]
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
    IsLocalRing (AdjoinRoot g) := by
  set B := AdjoinRoot g
  set J := Ideal.map (AdjoinRoot.of g) (maximalIdeal A) with hJ_def

  have e : B ⧸ J ≃+* (ResidueField A)[X] ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))} :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) g

  have hmax_span : (Ideal.span ({g.map (Ideal.Quotient.mk (maximalIdeal A))} :
      Set ((ResidueField A)[X]))).IsMaximal :=
    @AdjoinRoot.span_maximal_of_irreducible (ResidueField A) _ _ ⟨hg_irred_map⟩
  have hfield_quot : IsField ((ResidueField A)[X] ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax_span

  have hfield_BJ : IsField (B ⧸ J) := e.toMulEquiv.isField hfield_quot

  have hJ_max : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield_BJ


  apply IsLocalRing.of_unique_max_ideal
  exact ⟨J, hJ_max, fun M hM => by
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    haveI : M.IsMaximal := hM
    have hcomap_max := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := B) M
    have hcomap_eq := IsLocalRing.eq_maximalIdeal hcomap_max
    have h_le : maximalIdeal A ≤ Ideal.comap (algebraMap A B) M := hcomap_eq ▸ le_refl _
    have hJ_le_M : J ≤ M := Ideal.map_le_iff_le_comap.mpr h_le
    exact (hJ_max.eq_of_le hM.ne_top hJ_le_M).symm⟩

lemma adjoinRoot_of_injective_of_monic
    {A : Type*} [CommRing A] [IsDomain A]
    {g : Polynomial A} (hg : g.Monic) (hdeg : 0 < g.natDegree) :
    Function.Injective (AdjoinRoot.of g) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [RingHom.mem_ker] at ha
  change AdjoinRoot.mk g (Polynomial.C a) = 0 at ha
  rw [AdjoinRoot.mk_eq_zero] at ha
  obtain ⟨q, hq⟩ := ha
  by_cases ha0 : a = 0
  · simp [ha0]
  · exfalso
    have hCa_ne : Polynomial.C a ≠ 0 := Polynomial.C_ne_zero.mpr ha0
    have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hCa_ne hq
    have h2 : (g * q).natDegree = g.natDegree + q.natDegree :=
      Polynomial.natDegree_mul hg.ne_zero hq_ne
    rw [← hq] at h2
    have : (Polynomial.C a).natDegree = 0 := Polynomial.natDegree_C a
    omega

lemma natDegree_pos_of_monic_irred_map
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {g : Polynomial A} (hg_monic : g.Monic)
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A)))) :
    0 < g.natDegree := by
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have hd0 : g.natDegree = 0 := h
  have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg_monic hd0
  rw [hg1, Polynomial.map_one] at hg_irred_map
  exact not_irreducible_one hg_irred_map

lemma adjoinRoot_map_maximalIdeal_isMaximal
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) [IsDomain (AdjoinRoot g)]
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A)))) :
    (Ideal.map (AdjoinRoot.of g) (maximalIdeal A)).IsMaximal := by
  set B := AdjoinRoot g
  set J := Ideal.map (AdjoinRoot.of g) (maximalIdeal A)
  have e : B ⧸ J ≃+* (ResidueField A)[X] ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))} :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) g
  have hmax_span : (Ideal.span ({g.map (Ideal.Quotient.mk (maximalIdeal A))} :
      Set ((ResidueField A)[X]))).IsMaximal :=
    @AdjoinRoot.span_maximal_of_irreducible (ResidueField A) _ _ ⟨hg_irred_map⟩
  exact Ideal.Quotient.maximal_of_isField J
    (e.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax_span))

theorem adjoinRoot_isDVR_of_irred_map
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) (hg_monic : g.Monic) [IsDomain (AdjoinRoot g)]
    [Module.Finite A (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
    IsDiscreteValuationRing (AdjoinRoot g) := by
  set B := AdjoinRoot g

  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B


  have hnotfield : ¬ IsField B := by
    intro hfield
    have hdeg := natDegree_pos_of_monic_irred_map hg_monic hg_irred_map
    have hinj := adjoinRoot_of_injective_of_monic hg_monic hdeg
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)

  have hJ_max := adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map

  have h_max_eq : maximalIdeal B = Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal hJ_max).symm

  have hprinc : Submodule.IsPrincipal (maximalIdeal B) := h_max_eq ▸ inferInstance

  exact ((IsDiscreteValuationRing.TFAE B hnotfield).out 4 0).mp hprinc

theorem adjoinRoot_isLocalHom_of_irred_map
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) (hg_monic : g.Monic) [IsDomain (AdjoinRoot g)]
    [Module.Finite A (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
    IsLocalHom (AdjoinRoot.of g) := by

  apply ((local_hom_TFAE (AdjoinRoot.of g)).out 3 0).mp

  have hJ_max := adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map
  have h_max_eq : maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal hJ_max).symm
  rw [h_max_eq]
  exact Ideal.le_comap_map

theorem adjoinRoot_maxIdeal_eq_map_of_irred
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) (hg_monic : g.Monic) [IsDomain (AdjoinRoot g)]
    [Module.Finite A (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]
    (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
    IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) := by
  exact (IsLocalRing.eq_maximalIdeal
    (adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map)).symm

theorem adjoinRoot_dvr_of_irreducible_lift
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A]
    (gbar : (ResidueField A)[X]) (hgbar_monic : gbar.Monic) (hgbar_irred : Irreducible gbar)
    (hgbar_sep : gbar.Separable) :
    ∃ (g : Polynomial A) (_ : g.Monic) (_ : g.map (residue A) = gbar)
      (_ : IsDomain (AdjoinRoot g))
      (_ : IsDiscreteValuationRing (AdjoinRoot g))
      (_ : IsLocalHom (AdjoinRoot.of g))
      (_ : Module.Finite A (AdjoinRoot g)),
      ∃ (hAlg : Algebra (ResidueField A) (ResidueField (AdjoinRoot g)))
        (_ : @FiniteDimensional (ResidueField A) (ResidueField (AdjoinRoot g)) _ _ hAlg.toModule)
        (_ : @Algebra.IsSeparable (ResidueField A) (ResidueField (AdjoinRoot g)) _ _ hAlg),
      Nonempty (ResidueField (AdjoinRoot g) ≃+* AdjoinRoot gbar) := by

  have hlift : gbar ∈ lifts (residue A) :=
    (lifts_iff_coeff_lifts gbar).mpr (fun n => residue_surjective (gbar.coeff n))
  obtain ⟨g, hmap, hg_deg, hg_monic⟩ := lifts_and_natDegree_eq_and_monic hlift hgbar_monic
  have hgbar_ne : gbar ≠ 0 := hgbar_irred.ne_zero

  have hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A))) :=
    hmap ▸ hgbar_irred
  have hg_irred : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Ideal.Quotient.mk (maximalIdeal A)) g hg_monic hg_irred_map
  have hg_prime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hg_irred
  haveI hdom : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hg_prime

  haveI hfin : Module.Finite A (AdjoinRoot g) := hg_monic.finite_adjoinRoot

  haveI : IsLocalRing (AdjoinRoot g) :=
    adjoinRoot_isLocalRing_of_irred_map A g hg_monic hg_irred_map
  have hDVR : IsDiscreteValuationRing (AdjoinRoot g) :=
    adjoinRoot_isDVR_of_irred_map A g hg_monic hg_irred_map
  have hLH : IsLocalHom (AdjoinRoot.of g) :=
    adjoinRoot_isLocalHom_of_irred_map A g hg_monic hg_irred_map


  have h_max_eq : maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    adjoinRoot_maxIdeal_eq_map_of_irred A g hg_monic hg_irred_map
  set B := AdjoinRoot g


  have e1 : B ⧸ maximalIdeal B ≃+* B ⧸ Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    Ideal.quotEquivOfEq h_max_eq

  have e2 : (B ⧸ Ideal.map (AdjoinRoot.of g) (maximalIdeal A)) ≃+*
    (Polynomial (ResidueField A) ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) :=
    (AdjoinRoot.quotientIso A g).toRingEquiv

  have e3 : (Polynomial (ResidueField A) ⧸
    Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) ≃+*
    AdjoinRoot gbar :=
    Ideal.quotEquivOfEq (congr_arg (fun p => Ideal.span {p}) hmap)


  have iso : ResidueField B ≃+* AdjoinRoot gbar := e1.trans (e2.trans e3)

  set k := ResidueField A
  haveI : Fact (Irreducible gbar) := ⟨hgbar_irred⟩


  let algMap_k_adjgbar : k →+* AdjoinRoot gbar :=
    (AdjoinRoot.mk gbar).comp (Polynomial.C)
  let hAlg : Algebra k (ResidueField B) :=
    RingHom.toAlgebra (iso.symm.toRingHom.comp algMap_k_adjgbar)
  have hFD : @FiniteDimensional k (ResidueField B) _ _ hAlg.toModule := by

    have algEquiv : @AlgEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _ :=
      @AlgEquiv.ofRingEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _
        (f := iso) (fun x => by
          show iso (iso.symm ((algebraMap k (AdjoinRoot gbar)) x)) =
            (algebraMap k (AdjoinRoot gbar)) x
          simp)
    haveI : Module.Finite k (AdjoinRoot gbar) :=
      (AdjoinRoot.powerBasis hgbar_ne).finite
    exact @Module.Finite.equiv k (AdjoinRoot gbar) (ResidueField B) _
      inferInstance inferInstance inferInstance hAlg.toModule _
      algEquiv.symm.toLinearEquiv
  haveI hSep_adj : Algebra.IsSeparable k (AdjoinRoot gbar) := by
    open IntermediateField in
    have hSepRoot : IsSeparable k (AdjoinRoot.root gbar) := by
      unfold IsSeparable
      rw [AdjoinRoot.minpoly_root hgbar_ne]
      simp [hgbar_monic.leadingCoeff]
      exact hgbar_sep
    haveI : Algebra.IsSeparable k ↥k⟮AdjoinRoot.root gbar⟯ :=
      (isSeparable_adjoin_simple_iff_isSeparable k (AdjoinRoot gbar)).mpr hSepRoot
    exact Algebra.IsSeparable.of_algHom k (↥k⟮AdjoinRoot.root gbar⟯)
      ((IntermediateField.equivOfEq (IntermediateField.adjoin_root_eq_top gbar)).trans
        IntermediateField.topEquiv).symm.toAlgHom
  have hSep : @Algebra.IsSeparable k (ResidueField B) _ _ hAlg := by
    have algEquiv : @AlgEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _ :=
      @AlgEquiv.ofRingEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _
        (f := iso) (fun x => by
          show iso (iso.symm ((algebraMap k (AdjoinRoot gbar)) x)) =
            (algebraMap k (AdjoinRoot gbar)) x
          simp)
    exact @Algebra.IsSeparable.of_algHom k _ (ResidueField B) (AdjoinRoot gbar)
      _ _ hAlg _ algEquiv.toAlgHom _


  exact ⟨g, hg_monic, hmap, hdom, hDVR, hLH, hfin, hAlg, hFD, hSep, ⟨iso⟩⟩


theorem finiteDimensional_residueField_of_finite_dvr
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B] :
    FiniteDimensional (ResidueField A) (ResidueField B) := by
  letI σ := IsLocalRing.residue A
  haveI : RingHomSurjective σ := ⟨Ideal.Quotient.mk_surjective⟩
  have hcompat : ∀ a : A, (IsLocalRing.residue B) ((algebraMap A B) a) =
      (algebraMap (ResidueField A) (ResidueField B)) ((IsLocalRing.residue A) a) :=
    fun a => RingHom.congr_fun (IsLocalRing.ResidueField.map_comp_residue (algebraMap A B)).symm a
  let f : B →ₛₗ[σ] ResidueField B := {
    toFun := IsLocalRing.residue B
    map_add' := map_add _
    map_smul' := fun a b => by
      simp only [σ, Algebra.smul_def, map_mul]
      rw [hcompat a]
  }
  exact Module.Finite.of_surjective f Ideal.Quotient.mk_surjective

theorem adjoinRoot_module_finite_of_monic
    {A : Type*} [CommRing A] (g : Polynomial A) (hg : g.Monic) :
    Module.Finite A (AdjoinRoot g) :=
  hg.finite_adjoinRoot

theorem adjoinRoot_isDomain_of_irreducible_mod
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (g : Polynomial A) (hg : g.Monic)
    (hirr : Irreducible (g.map (residue A))) :
    IsDomain (AdjoinRoot g) :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue A) g hg hirr))

theorem finrank_adjoinRoot_of_monic
    {A : Type*} [CommRing A] [IsDomain A]
    (g : Polynomial A) (hg : g.Monic) :
    Module.finrank A (AdjoinRoot g) = g.natDegree := by
  rw [(AdjoinRoot.powerBasis' hg).finrank, AdjoinRoot.powerBasis'_dim]

theorem surjective_of_range_sup_maximalIdeal_smul_eq_top
    {A : Type*} [CommRing A] [IsLocalRing A]
    {C : Type*} [CommRing C] [Algebra A C]
    {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (φ : C →ₐ[A] B)
    (hsup : LinearMap.range φ.toLinearMap ⊔
      IsLocalRing.maximalIdeal A • ⊤ = ⊤) :
    Function.Surjective φ := by
  intro b
  have hJ : IsLocalRing.maximalIdeal A ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have htop_le : (⊤ : Submodule A B) ≤ LinearMap.range φ.toLinearMap ⊔
      IsLocalRing.maximalIdeal A • ⊤ := le_of_eq hsup.symm
  have hle := @Submodule.le_of_le_smul_of_le_jacobson_bot A B _ _ _
    (IsLocalRing.maximalIdeal A) (LinearMap.range φ.toLinearMap) ⊤
    Module.Finite.fg_top hJ htop_le
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (hle (Submodule.mem_top : b ∈ ⊤))
  exact ⟨c, hc⟩

theorem injective_of_surjective_of_finrank_eq_of_domain
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Type*} [CommRing C] [IsDomain C] [Algebra A C] [Module.Finite A C]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (φ : C →ₐ[A] B)
    (hrank : Module.finrank A C = Module.finrank A B)
    (hsurj : Function.Surjective φ) :
    Function.Injective φ := by
  by_cases hinj_alg : Function.Injective (algebraMap A C)
  ·
    haveI : NoZeroSMulDivisors A C := by
      constructor
      intro a c hac
      simp only [Algebra.smul_def] at hac
      rcases mul_eq_zero.mp hac with ha | hc
      · left; exact hinj_alg (ha.trans (map_zero _).symm)
      · right; exact hc
    haveI : Module.IsTorsionFree A C := FaithfulSMul.to_isTorsionFree A C
    haveI : Module.Free A C := Module.free_of_finite_type_torsion_free' (R := A) (M := C)
    let K := LinearMap.ker φ.toLinearMap
    have hrn := Submodule.finrank_quotient_add_finrank K
    have hfq : Module.finrank A (C ⧸ K) = Module.finrank A B := by
      have e1 := LinearMap.quotKerEquivRange φ.toLinearMap
      rw [LinearMap.range_eq_top.mpr hsurj] at e1
      exact (e1.trans (Submodule.topEquiv (R := A) (M := B))).finrank_eq
    have hfk : Module.finrank A K = 0 := by omega
    haveI : Module.IsTorsionFree A K := by
      constructor
      intro r hr x y hxy
      exact Subtype.ext (Module.IsTorsionFree.isSMulRegular (M := C) hr (Subtype.ext_iff.mp hxy))
    haveI : Module.Free A K := Module.free_of_finite_type_torsion_free' (R := A) (M := K)
    have hK_bot : K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : K) = 0 :=
        ((Module.finrank_eq_zero_iff_of_free A K).mp hfk).eq_zero _
      simpa using this
    exact LinearMap.ker_eq_bot.mp hK_bot
  ·
    have hker_ne : RingHom.ker (algebraMap A C) ≠ ⊥ := by
      rwa [Ne, ← RingHom.injective_iff_ker_eq_bot]
    have hker_prime : (RingHom.ker (algebraMap A C)).IsPrime := RingHom.ker_isPrime _
    have hker_max : RingHom.ker (algebraMap A C) = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (hker_prime.isMaximal hker_ne)
    have hC_field : IsField C := by
      have hle : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A C) := hker_max ▸ le_refl _
      let hlift := fun a (ha : a ∈ IsLocalRing.maximalIdeal A) => RingHom.mem_ker.mp (hle ha)
      let f := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A C) hlift
      letI : Algebra (IsLocalRing.ResidueField A) C := f.toAlgebra
      haveI : IsScalarTower A (IsLocalRing.ResidueField A) C := by
        apply IsScalarTower.of_algebraMap_eq
        intro a
        exact (Ideal.Quotient.lift_mk _ _ hlift : f _ = _).symm
      haveI : Module.Finite (IsLocalRing.ResidueField A) C :=
        Module.Finite.of_restrictScalars_finite A _ C
      exact isField_of_isIntegral_of_isField' (Field.toIsField (IsLocalRing.ResidueField A))
    letI := hC_field.toField
    exact φ.toRingHom.injective


set_option maxHeartbeats 3200000 in
theorem surjective_adjoinRoot_to_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (g : Polynomial A) (α : B) (hα_aeval : Polynomial.aeval α g = 0)
    (hg_monic : g.Monic) (hg_irr : Irreducible (g.map (IsLocalRing.residue A)))
    (hfinrank : Module.finrank A (AdjoinRoot g) = Module.finrank A B) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.map (algebraMap A B)
      (IsLocalRing.maximalIdeal A))).comp
      (AdjoinRoot.liftHom g α hα_aeval).toRingHom) := by
  haveI : Fact (Irreducible (g.map (IsLocalRing.residue A))) := ⟨hg_irr⟩
  set m := IsLocalRing.maximalIdeal A with hm_def
  set J := Ideal.map (algebraMap A B) m with hJ_def
  set q : B →+* B ⧸ J := Ideal.Quotient.mk J
  set phi := AdjoinRoot.liftHom g α hα_aeval

  have hkill : ∀ a ∈ m, (q.comp (algebraMap A B)) a = 0 := fun a ha => by
    show q (algebraMap A B a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_map_of_mem _ ha
  set algMap_k : IsLocalRing.ResidueField A →+* B ⧸ J :=
    Ideal.Quotient.lift m (q.comp (algebraMap A B)) hkill
  letI instAlg : Algebra (IsLocalRing.ResidueField A) (B ⧸ J) := algMap_k.toAlgebra
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algMap_k (IsLocalRing.residue A a) = algebraMap A (B ⧸ J) a
      exact (Ideal.Quotient.lift_mk _ _ _ : algMap_k _ = _)

  set gbar := g.map (IsLocalRing.residue A)
  have haeval : (Polynomial.aeval (R := IsLocalRing.ResidueField A) (A := B ⧸ J) (q α)) gbar = 0 := by
    simp only [Polynomial.aeval_def, gbar]
    rw [show (g.map (IsLocalRing.residue A)).eval₂
          (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)) (q α) =
        g.eval₂ ((algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp (IsLocalRing.residue A))
          (q α) from Polynomial.eval₂_map _ _ _]
    have hcomp : (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp
        (IsLocalRing.residue A) = q.comp (algebraMap A B) := by
      ext a; simp only [RingHom.comp_apply]; exact Ideal.Quotient.lift_mk _ _ _
    rw [hcomp, ← Polynomial.hom_eval₂ g (algebraMap A B) q α,
        show g.eval₂ (algebraMap A B) α = 0 from by rwa [← Polynomial.aeval_def], map_zero]

  set f := AdjoinRoot.liftHom gbar (q α) haeval

  haveI : Nontrivial (B ⧸ J) := by
    rw [Ideal.Quotient.nontrivial_iff]; intro hJ
    have h1 : (⊤ : Submodule A B) ≤ m • ⊤ := by
      rw [Ideal.smul_top_eq_map]; intro x _
      rw [Submodule.restrictScalars_mem]; change x ∈ J; rw [hJ]; trivial
    have h3 := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m ⊤
      Module.Finite.fg_top h1 (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact one_ne_zero (show (1 : B) = 0 by
      have := h3 ▸ (Submodule.mem_top : (1 : B) ∈ ⊤); rwa [Submodule.mem_bot] at this)

  have hf_inj : Function.Injective f := RingHom.injective f.toRingHom

  haveI : Module.Free A (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.isAdjoinRootMonic g hg_monic).powerBasis.basis
  have hndeg_pos : 0 < g.natDegree := by
    rw [← hg_monic.natDegree_map (IsLocalRing.residue A)]; exact hg_irr.natDegree_pos
  have hinj_alg : Function.Injective (algebraMap A B) := by
    by_contra h
    have hker : RingHom.ker (algebraMap A B) ≠ ⊥ := by
      rwa [Ne, ← RingHom.injective_iff_ker_eq_bot]
    obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [RingHom.mem_ker] at ha_mem
    have : Module.finrank A B = 0 :=
      (Module.finrank_eq_zero_iff (R := A) (M := B)).mpr
        fun x => ⟨a, ha_ne, by simp [Algebra.smul_def, ha_mem]⟩
    linarith [(AdjoinRoot.isAdjoinRootMonic g hg_monic).finrank]
  haveI : NoZeroSMulDivisors A B := by
    constructor; intro a b hab; simp only [Algebra.smul_def] at hab
    rcases mul_eq_zero.mp hab with ha | hb
    · left; exact hinj_alg (ha.trans (map_zero _).symm)
    · right; exact hb
  haveI : Module.IsTorsionFree A B := FaithfulSMul.to_isTorsionFree A B
  haveI : Module.Free A B := Module.free_of_finite_type_torsion_free' (R := A) (M := B)

  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (AdjoinRoot gbar) :=
    (AdjoinRoot.powerBasis (hg_irr.ne_zero)).finite
  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (B ⧸ J) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hfr_eq : Module.finrank (IsLocalRing.ResidueField A) (AdjoinRoot gbar) =
      Module.finrank (IsLocalRing.ResidueField A) (B ⧸ J) := by
    have h1 : Module.finrank (IsLocalRing.ResidueField A) (AdjoinRoot gbar) = gbar.natDegree :=
      (AdjoinRoot.powerBasis (hg_irr.ne_zero)).finrank.trans
        (AdjoinRoot.powerBasis_dim (hg_irr.ne_zero))
    have h2 := hg_monic.natDegree_map (IsLocalRing.residue A)
    have h4 := (AdjoinRoot.isAdjoinRootMonic g hg_monic).finrank

    have h3 := @IsLocalRing.finrank_quotient_map A B _ _ _ _ _ _

    have : Module.finrank (IsLocalRing.ResidueField A) (B ⧸ J) =
        Module.finrank A B := by
      have : instAlg = Ideal.Quotient.algebraQuotientMapQuotient := by
        apply Algebra.algebra_ext
        intro c
        induction c using Quotient.inductionOn' with
        | h a =>
          show algMap_k (Ideal.Quotient.mk m a) = _
          exact Ideal.Quotient.lift_mk _ _ _
      rw [this]; exact h3
    linarith
  have hf_surj : Function.Surjective f := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr_eq
      (f := f.toLinearMap)).mp hf_inj
    exact this

  intro b
  obtain ⟨x, hx⟩ := hf_surj b
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (IsLocalRing.residue A)
    Ideal.Quotient.mk_surjective p
  refine ⟨AdjoinRoot.mk g P, ?_⟩

  rw [RingHom.comp_apply, ← hx, ← hP]


  show q ((AdjoinRoot.liftHom g α hα_aeval) (AdjoinRoot.mk g P)) =
    (AdjoinRoot.liftHom gbar (q α) haeval) (AdjoinRoot.mk gbar (Polynomial.map (IsLocalRing.residue A) P))
  erw [AdjoinRoot.liftHom_mk (f := g) (g := P), AdjoinRoot.liftHom_mk (f := gbar)]

  simp only [Polynomial.aeval_def]
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp
      (IsLocalRing.residue A) = q.comp (algebraMap A B) := by
    ext a; simp only [RingHom.comp_apply]; exact Ideal.Quotient.lift_mk _ _ _
  rw [hcomp, ← Polynomial.hom_eval₂ P (algebraMap A B) q α]

theorem range_sup_maximalIdeal_smul_eq_top_of_adjoinRoot_liftHom
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (g : Polynomial A) (α : B) (hα_aeval : Polynomial.aeval α g = 0)
    (hg_monic : g.Monic) (hg_irr : Irreducible (g.map (IsLocalRing.residue A)))
    (hfinrank : Module.finrank A (AdjoinRoot g) = Module.finrank A B) :
    LinearMap.range (AdjoinRoot.liftHom g α hα_aeval).toLinearMap ⊔
      IsLocalRing.maximalIdeal A • ⊤ = ⊤ := by
  set φ := AdjoinRoot.liftHom g α hα_aeval
  set m := IsLocalRing.maximalIdeal A

  rw [show (m • ⊤ : Submodule A B) = Submodule.restrictScalars A
    (Ideal.map (algebraMap A B) m) from Ideal.smul_top_eq_map m]


  rw [eq_top_iff]

  intro b _
  rw [Submodule.mem_sup]
  set J := Ideal.map (algebraMap A B) m
  set q : B →+* B ⧸ J := Ideal.Quotient.mk J


  have hsurj : Function.Surjective (q.comp φ.toRingHom) :=
    surjective_adjoinRoot_to_quotient g α hα_aeval hg_monic hg_irr hfinrank
  obtain ⟨c, hc⟩ := hsurj (q b)


  refine ⟨φ c, LinearMap.mem_range.mpr ⟨c, rfl⟩, b - φ c, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem]
  have hc' : q (φ c) = q b := hc
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hc'
  exact J.neg_mem_iff.mp (show -(b - φ c) ∈ J by rwa [neg_sub])


lemma adjoinRoot_minpoly_ringEquiv {k : Type*} [Field k] {l : Type*} [Field l]
    [Algebra k l] [FiniteDimensional k l]
    (α : l) (hα : IntermediateField.adjoin k ({α} : Set l) = ⊤)
    (hint : IsIntegral k α) :
    Nonempty (AdjoinRoot (minpoly k α) ≃+* l) := by
  haveI : Fact (Irreducible (minpoly k α)) := ⟨minpoly.irreducible hint⟩
  let φ := AdjoinRoot.liftHom (minpoly k α) α (minpoly.aeval k α)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have _hfinA : FiniteDimensional k (AdjoinRoot (minpoly k α)) :=
    (AdjoinRoot.powerBasis' (minpoly.monic hint)).finite
  have hdim : Module.finrank k (AdjoinRoot (minpoly k α)) = Module.finrank k l := by
    rw [(AdjoinRoot.powerBasis' (minpoly.monic hint)).finrank]
    simp only [AdjoinRoot.powerBasis']
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := φ.toLinearMap)).mp hinj
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).toRingEquiv⟩

section ResidueHelpers

variable {A : Type*} [CommRing A] [IsLocalRing A]
  {B : Type*} [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

lemma residue_comp_algebraMap_eq :
    (residue B).comp (algebraMap A B) =
    (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) := by
  ext a; rfl

lemma residue_aeval_eq (p : A[X]) (b : B) :
    residue B (aeval b p) = aeval (residue B b) (p.map (residue A)) := by
  simp only [aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂,
    residue_comp_algebraMap_eq]

lemma adjoin_residue_top_of_adjoin_top
    (α : B) (htop : Algebra.adjoin A ({α} : Set B) = ⊤) :
    Algebra.adjoin (ResidueField A) ({residue B α} : Set (ResidueField B)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, rfl⟩ := residue_surjective x
  have hb : b ∈ Algebra.adjoin A ({α} : Set B) := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb ⊢
  obtain ⟨p, rfl⟩ := hb
  show residue B ((aeval α) p) ∈ (aeval (residue B α)).range
  rw [residue_aeval_eq]
  exact ⟨p.map (residue A), rfl⟩

end ResidueHelpers

section ResidueFieldFunctorFullFaithfulness

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]

variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]

theorem dvr_extension_henselian
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    HenselianLocalRing B := by
  have hH := IsAdicComplete.henselianRing B (IsLocalRing.maximalIdeal B)
  exact {
    is_henselian := fun f hfm a₀ hfa₀ hunit => by
      have hunit' : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
          (Polynomial.eval a₀ (Polynomial.derivative f))) :=
        hunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))
      exact hH.is_henselian f hfm a₀ hfa₀ hunit'
  }

def residueFieldFunctorAlg (φ : B₁ →ₐ[A] B₂) :
    ResidueField B₁ →ₐ[ResidueField A] ResidueField B₂ :=
  { @ResidueField.map B₁ B₂ _ _ _ _ φ.toRingHom (algHom_dvr_isLocalHom φ) with
    commutes' := by
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      show (@ResidueField.map B₁ B₂ _ _ _ _ φ.toRingHom (algHom_dvr_isLocalHom φ))
        (algebraMap (ResidueField A) (ResidueField B₁) (residue A a)) =
        algebraMap (ResidueField A) (ResidueField B₂) (residue A a)
      change (residue B₂) (φ (algebraMap A B₁ a)) = (residue B₂) (algebraMap A B₂ a)
      rw [φ.commutes] }


end ResidueFieldFunctorFullFaithfulness

section ResidueFieldFunctorEssentialSurjectivity

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]

theorem residueFieldFunctor_essential_surjectivity
    (l : Type) [Field l] [Algebra (ResidueField A) l]
    [FiniteDimensional (ResidueField A) l] [Algebra.IsSeparable (ResidueField A) l] :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)) (_ : Module.Finite A B),


      ∃ (hAlg : Algebra (ResidueField A) (ResidueField B))
        (_ : @FiniteDimensional (ResidueField A) (ResidueField B) _ _ hAlg.toModule)
        (_ : @Algebra.IsSeparable (ResidueField A) (ResidueField B) _ _ hAlg),

      Nonempty (ResidueField B ≃+* l) := by

  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) l

  have hint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  have hgbar_monic := minpoly.monic hint
  have hgbar_irred := minpoly.irreducible hint
  have hgbar_sep : (minpoly (ResidueField A) α).Separable :=
    (Algebra.IsSeparable.isSeparable' α : IsSeparable (ResidueField A) α)


  obtain ⟨g, _, _, hID, hDVR, hLH, hMF, hAlg, hFD, hSep, ⟨e1⟩⟩ :=
    adjoinRoot_dvr_of_irreducible_lift A (minpoly (ResidueField A) α)
      hgbar_monic hgbar_irred hgbar_sep

  obtain ⟨e2⟩ := adjoinRoot_minpoly_ringEquiv α hα hint

  exact ⟨AdjoinRoot g, inferInstance, hID, hDVR, inferInstance, hLH, hMF,
    hAlg, hFD, hSep, ⟨e1.trans e2⟩⟩

end ResidueFieldFunctorEssentialSurjectivity

section ResidueFieldFunctorInjectivity

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]

variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]

variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]


end ResidueFieldFunctorInjectivity

section ResidueFieldFunctorEquivalence

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]

variable {B₁ : Type} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]

variable {B₂ : Type} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]


end ResidueFieldFunctorEquivalence

end
