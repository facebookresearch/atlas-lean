/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.HenselLemmas
import Atlas.NumberTheoryI.code.ScalingStep
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity

open Polynomial IsLocalRing


section HenselIII

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]



end HenselIII


section HenselKurschak

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem hensel_kurschak_scaling_step
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (f : K[X])
    (hirr : Irreducible f)
    (hlead : ∃ a : A, algebraMap A K a = f.leadingCoeff)
    (hconst : ∃ a : A, algebraMap A K a = f.coeff 0)
    (hnotinA : ¬∃ g : A[X], f = Polynomial.map (algebraMap A K) g) :
    ∃ (g : A[X]),
      Irreducible g ∧
      g.coeff 0 ∈ maximalIdeal A ∧
      g.coeff g.natDegree ∈ maximalIdeal A ∧
      (∃ i, ¬(g.coeff i ∈ maximalIdeal A)) :=
  hensel_kurschak_scaling_step' f hirr hlead hconst hnotinA


end HenselKurschak


section NormIntegrality

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]

omit [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] in
theorem norm_eq_minpoly_const_power
    (α : L) :
    ∃ e : ℕ, 0 < e ∧ Algebra.norm K α =
      (-1) ^ (Module.finrank K L) * (minpoly K α).eval 0 ^ e := by
  open IntermediateField in
  haveI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  have hα : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨Module.finrank K⟮α⟯ L, Module.finrank_pos (R := ↥K⟮α⟯) (M := L), ?_⟩
  rw [Algebra.norm_eq_norm_adjoin K α]
  set pb := IntermediateField.adjoin.powerBasis hα
  rw [← IntermediateField.adjoin.powerBasis_gen hα]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb]
  rw [IntermediateField.adjoin.powerBasis_gen hα,
      IntermediateField.minpoly_gen K α]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [mul_pow, ← pow_mul]
  have h1 : pb.dim = (minpoly K α).natDegree := IntermediateField.adjoin.powerBasis_dim hα
  have h2 : Module.finrank K ↥K⟮α⟯ = (minpoly K α).natDegree :=
    IntermediateField.adjoin.finrank hα
  rw [h1, ← h2, Module.finrank_mul_finrank K ↥K⟮α⟯ L]

theorem norm_integral_of_integral
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    (α : L) (hα : IsIntegral A α) :
    ∃ a : A, algebraMap A K a = Algebra.norm K α := by
  haveI : IsIntegrallyClosed A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hα)



end NormIntegrality


section IntegralClosureDVR

theorem isLocalRing_of_unique_maximal (R : Type*) [CommRing R] [IsDomain R]
    (𝔮 : Ideal R) (h𝔮 : 𝔮.IsMaximal)
    (huniq : ∀ (I : Ideal R), I.IsMaximal → I = 𝔮) : IsLocalRing R :=
  IsLocalRing.of_is_unit_or_is_unit_of_add_one (fun {a b} hab => by
    by_cases ha : a ∈ 𝔮
    · right
      have hb : b ∉ 𝔮 := fun hb =>
        h𝔮.ne_top ((Ideal.eq_top_iff_one 𝔮).mpr (hab ▸ 𝔮.add_mem ha hb))
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact hb (huniq M hM ▸ hle (Ideal.subset_span rfl))
    · left
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact ha (huniq M hM ▸ hle (Ideal.subset_span rfl)))

theorem isDVR_of_local_dedekind (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [IsLocalRing R] (hnotfield : ¬IsField R) :
    IsDiscreteValuationRing R :=
  (IsDiscreteValuationRing.TFAE R hnotfield |>.out 2 0).mp ‹_›

theorem maximal_lies_over_in_AKLB
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (B : Type*) [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔮 : Ideal B) (h𝔮 : 𝔮.IsMaximal) :
    Ideal.comap (algebraMap A B) 𝔮 = maximalIdeal A := by
  have hprime : (Ideal.comap (algebraMap A B) 𝔮).IsPrime :=
    Ideal.IsPrime.comap (algebraMap A B)
  have hne : Ideal.comap (algebraMap A B) 𝔮 ≠ ⊥ := by
    haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
    have h𝔮_ne_bot : 𝔮 ≠ ⊥ := by
      intro h𝔮_eq_bot
      have hBfield : IsField B := by
        rw [← not_not (a := IsField B)]
        intro hnotfield
        exact (Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 hnotfield) h𝔮_eq_bot
      haveI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
      have hinj : Function.Injective (algebraMap A B) := by
        have h1 : Function.Injective (algebraMap A L) := by
          rw [IsScalarTower.algebraMap_eq A K L]
          exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
        intro a b hab
        exact h1 (by simp [IsScalarTower.algebraMap_eq A B L, hab])
      exact IsDiscreteValuationRing.not_isField A
        (isField_of_isIntegral_of_isField hinj hBfield)
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮_ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem
      (IsIntegralClosure.isIntegral A L x)
  exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne hprime)

theorem two_maximal_ideals_give_coprime_factorization
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔮₁ 𝔮₂ : Ideal B)
    (h₁ : 𝔮₁.IsMaximal) (h₂ : 𝔮₂.IsMaximal) (_hne : 𝔮₁ ≠ 𝔮₂)
    (b : B) (hb₁ : b ∈ 𝔮₁) (hb₂ : b ∉ 𝔮₂)
    (hbint : IsIntegral A b)
    (_hirr : Irreducible (minpoly A b)) :
    ∃ (g_bar h_bar : (A ⧸ maximalIdeal A)[X]),
      Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A b)
        = g_bar * h_bar ∧
      IsCoprime g_bar h_bar ∧
      ¬IsUnit g_bar ∧ ¬IsUnit h_bar := by
  set 𝔭 := maximalIdeal A with h𝔭_def
  set f := minpoly A b with hf_def
  set π := Ideal.Quotient.mk 𝔭 with hπ_def
  set f_bar := Polynomial.map π f with hf_bar_def

  haveI h𝔭_max : 𝔭.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭

  have hcoeff0_in_p : f.coeff 0 ∈ 𝔭 := by

    have hmem : f.coeff 0 ∈ Ideal.comap (algebraMap A B) 𝔮₁ := by
      rw [Ideal.mem_comap]
      have heval_zero : (Ideal.Quotient.mk 𝔮₁) (algebraMap A B (f.coeff 0)) = 0 := by
        have h1 : (Ideal.Quotient.mk 𝔮₁) (Polynomial.aeval b f) = 0 := by
          rw [minpoly.aeval, map_zero]
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
            Ideal.Quotient.eq_zero_iff_mem.mpr hb₁, Polynomial.eval₂_at_zero] at h1
        exact h1
      rwa [Ideal.Quotient.eq_zero_iff_mem] at heval_zero

    rwa [maximal_lies_over_in_AKLB A K L B 𝔮₁ h₁] at hmem

  have hf_bar_ne_zero : f_bar ≠ 0 :=
    (Polynomial.Monic.map π (minpoly.monic hbint)).ne_zero

  have hroot0 : f_bar.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcoeff0_in_p
  have hd_pos : 0 < f_bar.rootMultiplicity 0 :=
    (Polynomial.rootMultiplicity_pos hf_bar_ne_zero).mpr hroot0

  obtain ⟨q, hfact, hq_ndvd⟩ :=
    f_bar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf_bar_ne_zero 0
  set d := f_bar.rootMultiplicity 0 with hd_def

  have hXC : (X : (A ⧸ 𝔭)[X]) - C 0 = X := by simp
  rw [hXC] at hfact hq_ndvd

  have hXd_not_unit : ¬IsUnit (X ^ d : (A ⧸ 𝔭)[X]) := by
    intro hu
    rw [Polynomial.isUnit_iff] at hu
    obtain ⟨r, _, hrp⟩ := hu
    have : (X ^ d : (A ⧸ 𝔭)[X]).natDegree = 0 := by rw [← hrp, Polynomial.natDegree_C]
    rw [Polynomial.natDegree_X_pow] at this
    omega

  have hq_not_unit : ¬IsUnit q := by
    intro hqu

    rw [Polynomial.isUnit_iff] at hqu
    obtain ⟨r, hr_unit, hrq⟩ := hqu


    have hcomap₂ : Ideal.comap (algebraMap A B) 𝔮₂ = 𝔭 :=
      maximal_lies_over_in_AKLB A K L B 𝔮₂ h₂
    have hlift_cond : ∀ a ∈ 𝔭, ((Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B)) a = 0 := by
      intro a ha
      simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      rwa [← Ideal.mem_comap, hcomap₂]
    set g := Ideal.Quotient.lift 𝔭 ((Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B)) hlift_cond

    have hg_comp : g.comp π = (Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B) :=
      Ideal.Quotient.lift_comp_mk 𝔭 _ hlift_cond

    set b_bar₂ := Ideal.Quotient.mk 𝔮₂ b with hb_bar₂_def
    have heval_fbar : Polynomial.eval₂ g b_bar₂ f_bar = 0 := by
      rw [hf_bar_def, Polynomial.eval₂_map, hg_comp]


      rw [← Polynomial.hom_eval₂ f (algebraMap A B) (Ideal.Quotient.mk 𝔮₂) b]


      have : Polynomial.eval₂ (algebraMap A B) b f = 0 := by
        rw [← Polynomial.aeval_def]; exact minpoly.aeval A b
      rw [this, map_zero]

    have heval_expand : g r * b_bar₂ ^ d = 0 := by
      rw [hfact, ← hrq, mul_comm] at heval_fbar
      rwa [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at heval_fbar

    have hgr_unit : IsUnit (g r) := g.isUnit_map hr_unit

    haveI : Nontrivial (B ⧸ 𝔮₂) := Ideal.Quotient.nontrivial_iff.mpr h₂.ne_top
    have hgr_ne_zero : g r ≠ 0 := hgr_unit.ne_zero

    have hbd_zero : b_bar₂ ^ d = 0 := by
      rcases mul_eq_zero.mp heval_expand with h | h
      · exact absurd h hgr_ne_zero
      · exact h

    haveI : IsDomain (B ⧸ 𝔮₂) := by
      exact Ideal.Quotient.isDomain 𝔮₂
    have hb_bar_zero : b_bar₂ = 0 :=
      (pow_eq_zero_iff (by omega : d ≠ 0)).mp hbd_zero

    exact hb₂ (Ideal.Quotient.eq_zero_iff_mem.mp hb_bar_zero)

  have hcoprime : IsCoprime q (X ^ d) :=
    Irreducible.coprime_pow_of_not_dvd d Polynomial.irreducible_X hq_ndvd

  exact ⟨q, X ^ d, by rw [hfact, mul_comm], hcoprime, hq_not_unit, hXd_not_unit⟩



end IntegralClosureDVR
