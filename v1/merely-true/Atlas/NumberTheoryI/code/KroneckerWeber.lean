/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Atlas.NumberTheoryI.code.GroupCounts
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Atlas.NumberTheoryI.code.AdicCompletionAlgebra
import Atlas.NumberTheoryI.code.KroneckerWeberLocal2
import Atlas.NumberTheoryI.code.ResidueFieldHelper
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field

import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Atlas.NumberTheoryI.code.CyclotomicDVRInstances

noncomputable section

namespace KroneckerWeber

class IsAbelianExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  comm : ∀ σ τ : (E ≃ₐ[F] E), σ * τ = τ * σ

class IsCyclicExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  isCyclic : IsCyclic (E ≃ₐ[F] E)

def LiesInCyclotomicExtension (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop :=
  ∃ (m : ℕ) (_ : m ≥ 1), Nonempty (K →ₐ[F] CyclotomicField m F)

instance IsAbelianExtension.toIsGalois (F E : Type*) [Field F] [Field E]
    [Algebra F E] [h : IsAbelianExtension F E] : IsGalois F E :=
  h.isGalois

theorem cyclotomic_prime_irreducible_padic (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (Polynomial.cyclotomic p ℚ_[p]) := by
  have heis_Z := cyclotomic_comp_X_add_one_isEisensteinAt p
  set g := (Polynomial.cyclotomic p ℤ_[p]).comp (Polynomial.X + Polynomial.C 1) with hg_def
  have hmap : g = Polynomial.map (algebraMap ℤ ℤ_[p])
      ((Polynomial.cyclotomic p ℤ).comp (Polynomial.X + Polynomial.C 1)) := by
    rw [hg_def, Polynomial.map_comp, Polynomial.map_cyclotomic]; congr 1
    simp [Polynomial.map_X, Polynomial.map_one]
  have hXC : (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 := by simp
  have hmaxZp : IsLocalRing.maximalIdeal ℤ_[p] = Ideal.span {(p : ℤ_[p])} :=
    PadicInt.maximalIdeal_eq_span_p
  have hinj : Function.Injective (algebraMap ℤ ℤ_[p]) := Int.cast_injective
  have heis_Zp : g.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
    refine ⟨?_, ?_, ?_⟩
    · have : g.Monic := (Polynomial.cyclotomic.monic p ℤ_[p]).comp (Polynomial.monic_X_add_C 1)
        (by rw [Polynomial.natDegree_X_add_C]; exact Nat.one_ne_zero)
      rw [this.leadingCoeff]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    · intro n hn
      rw [hmaxZp]
      rw [hmap] at hn ⊢
      rw [Polynomial.coeff_map, Ideal.mem_span_singleton]
      have hn' : n < ((Polynomial.cyclotomic p ℤ).comp
          (Polynomial.X + Polynomial.C 1)).natDegree := by
        rwa [Polynomial.natDegree_map_eq_of_injective hinj] at hn
      have hmem := heis_Z.mem (hXC ▸ hn')
      rw [hXC, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨algebraMap ℤ ℤ_[p] c, by rw [← hc]; simp [mul_comm]⟩
    · rw [hmaxZp, Polynomial.coeff_zero_eq_eval_zero, hg_def, Polynomial.eval_comp,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add,
          Polynomial.eval_one_cyclotomic_prime, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton]
      intro ⟨c, hc⟩
      have hp_ne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      have h1 : (p : ℤ_[p]) * ((p : ℤ_[p]) * c - 1) = 0 := by
        have : (p : ℤ_[p]) ^ 2 * c = (p : ℤ_[p]) * ((p : ℤ_[p]) * c) := by ring
        rw [mul_sub, mul_one, ← this, ← hc, sub_self]
      have h3 : (p : ℤ_[p]) * c - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hp_ne
      have h4 : (p : ℤ_[p]) * c = 1 := by rwa [sub_eq_zero] at h3
      exact PadicInt.prime_p.not_unit (IsUnit.of_mul_eq_one c h4)
  have hirr_g : Irreducible g :=
    heis_Zp.irreducible
      (Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]))
      ((Polynomial.cyclotomic.monic p ℤ_[p]).comp (Polynomial.monic_X_add_C 1)
        (by rw [Polynomial.natDegree_X_add_C]; exact Nat.one_ne_zero)).isPrimitive
      (by rw [Polynomial.natDegree_comp, Polynomial.natDegree_cyclotomic,
              Polynomial.natDegree_X_add_C]; simp [hp.out.pos])
  have hirr_Zp : Irreducible (Polynomial.cyclotomic p ℤ_[p]) := by
    let e := Polynomial.algEquivOfCompEqX
      (Polynomial.X + Polynomial.C 1 : Polynomial ℤ_[p]) (Polynomial.X - Polynomial.C 1)
      (by simp [Polynomial.add_comp, Polynomial.X_comp])
      (by simp [Polynomial.sub_comp, Polynomial.X_comp])
    rw [show Polynomial.cyclotomic p ℤ_[p] = e.symm (e (Polynomial.cyclotomic p ℤ_[p]))
        from (e.symm_apply_apply _).symm]
    have : e (Polynomial.cyclotomic p ℤ_[p]) = g := by
      simp only [e, Polynomial.algEquivOfCompEqX, hg_def]; rfl
    rw [this]
    exact (MulEquiv.irreducible_iff e.toMulEquiv.symm).mpr hirr_g
  rw [show Polynomial.cyclotomic p ℚ_[p] =
      Polynomial.map (algebraMap ℤ_[p] ℚ_[p]) (Polynomial.cyclotomic p ℤ_[p])
      from (Polynomial.map_cyclotomic p (algebraMap ℤ_[p] ℚ_[p])).symm]
  exact ((Polynomial.cyclotomic.monic p ℤ_[p]).irreducible_iff_irreducible_map_fraction_map).mp
    hirr_Zp

lemma hensel_padic_unit_root_p_eq_two
    (p : ℕ) [Fact (Nat.Prime p)]
    (L : Type*) [Field L] [Algebra ℚ_[p] L]
    [IsCyclotomicExtension {p} ℚ_[p] L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (hp : p = 2) :
    ∃ β : L, β ≠ 0 ∧
      β ^ (p - 1) = -(ζ - 1) ^ (p - 1) / algebraMap ℚ_[p] L (↑p : ℚ_[p]) := by
  subst hp
  have hζ_eq : ζ = -1 := by
    have hsq : ζ ^ 2 = 1 := hζ.pow_eq_one
    have hne : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have h : (ζ - 1) * (ζ + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · linear_combination h1
  refine ⟨1, one_ne_zero, ?_⟩
  simp only [hζ_eq, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[2] L).injective
  have hnum : -(-1 - 1 : L) = 2 := by ring
  rw [hnum]
  have halg : (algebraMap ℚ_[2] L) (↑(2 : ℕ) : ℚ_[2]) = (2 : L) := by
    simp [map_ofNat]
  rw [halg]
  exact (div_self (two_ne_zero' L)).symm

def geom_sum_prod {R : Type*} [CommRing R] (ζ : R) (p : ℕ) : R :=
  ∏ k ∈ Finset.range (p - 1), ∑ i ∈ Finset.range (k + 1), ζ ^ i

theorem cyclotomic_product_identity {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2)
    {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    (ζ - 1) ^ (p - 1) * geom_sum_prod ζ p = ↑p := by
  unfold geom_sum_prod
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hpn : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp0).symm
  have hprod := IsPrimitiveRoot.prod_one_sub_pow_eq_order (hpn ▸ hζ)
  have hfactor : ∀ k, (1 : R) - ζ ^ (k + 1) =
      (1 - ζ) * ∑ i ∈ Finset.range (k + 1), ζ ^ i := by
    intro k
    have := geom_sum_mul_neg ζ (k + 1)
    linear_combination -this
  simp_rw [hfactor] at hprod
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod
  have h1mz : (1 : R) - ζ = -(ζ - 1) := by ring
  rw [h1mz, neg_pow] at hprod
  have heven : Even (p - 1) := by
    rw [Nat.even_sub hp1.le]
    simp [hp.odd_of_ne_two hodd]
  rw [Even.neg_one_pow heven, one_mul] at hprod
  convert hprod using 1
  rw [Nat.cast_sub hp1.le]; ring

theorem isUnit_geom_sum_prod {L : Type*} [Field L]
    {p : ℕ}
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    IsUnit (geom_sum_prod ζ p) := by
  unfold geom_sum_prod
  rw [IsUnit.prod_iff]
  intro k hk
  rw [isUnit_iff_ne_zero]
  intro h0
  have := geom_sum_mul ζ (k + 1)
  rw [h0, zero_mul] at this
  have hone : ζ ^ (k + 1) = 1 := by rwa [eq_comm, sub_eq_zero] at this
  have hk' := Finset.mem_range.mp hk
  exact hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega) hone






theorem eisenstein_element_generates_cyclotomic (p : ℕ) [hp : Fact (Nat.Prime p)]
    (L : Type*) [Field L] [Algebra ℚ_[p] L]
    [IsCyclotomicExtension {p} ℚ_[p] L]
    (α : L) (hα : α ^ (p - 1) + algebraMap ℚ_[p] L (↑p : ℚ_[p]) = 0) :
    Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤ := by
  open Polynomial in
  have hprime := hp.out
  have hp0 : p - 1 ≠ 0 := by have := hprime.one_lt; omega
  haveI : NeZero p := ⟨hprime.ne_zero⟩
  haveI : FiniteDimensional ℚ_[p] L :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ_[p] L

  have hirr_Zp : Irreducible (X ^ (p - 1) + C (p : ℤ_[p])) := by
    have heis : (X ^ (p - 1) + C (p : ℤ_[p])).IsEisensteinAt
        (IsLocalRing.maximalIdeal ℤ_[p]) := by
      constructor
      · rw [(monic_X_pow_add_C _ hp0).leadingCoeff]
        exact fun h => (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
          (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
      · intro n hn
        rw [natDegree_X_pow_add_C] at hn
        rw [PadicInt.maximalIdeal_eq_span_p]
        have hne : ¬(n = p - 1) := by omega
        simp only [coeff_add, coeff_X_pow, hne, ite_false, zero_add]
        by_cases hn0 : n = 0
        · subst hn0; simp [Ideal.mem_span_singleton]
        · simp [hn0]
      · rw [PadicInt.maximalIdeal_eq_span_p]
        have hne : ¬(0 = p - 1) := by omega
        simp only [coeff_add, coeff_X_pow, hne, ite_false, zero_add, coeff_C_zero]
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        intro ⟨c, hc⟩
        have hp_ne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hprime.ne_zero
        have h1 : (p : ℤ_[p]) * ((p : ℤ_[p]) * c - 1) = 0 := by
          have : (p : ℤ_[p]) ^ 2 * c = (p : ℤ_[p]) * ((p : ℤ_[p]) * c) := by ring
          rw [mul_sub, mul_one, ← this, ← hc, sub_self]
        have h3 : (p : ℤ_[p]) * c - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hp_ne
        have h4 : (p : ℤ_[p]) * c = 1 := by rwa [sub_eq_zero] at h3
        exact PadicInt.prime_p.not_unit (IsUnit.of_mul_eq_one c h4)
    exact heis.irreducible
      (Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]))
      (monic_X_pow_add_C _ hp0).isPrimitive
      (by rw [natDegree_X_pow_add_C]; omega)

  have hirr_Qp : Irreducible (X ^ (p - 1) + C (p : ℚ_[p])) := by
    rw [show X ^ (p - 1) + C (p : ℚ_[p]) =
        map (algebraMap ℤ_[p] ℚ_[p]) (X ^ (p - 1) + C (p : ℤ_[p]))
        from by simp [map_X]]
    exact ((monic_X_pow_add_C (p : ℤ_[p]) hp0).irreducible_iff_irreducible_map_fraction_map).mp
      hirr_Zp

  have haeval : aeval α (X ^ (p - 1) + C (p : ℚ_[p])) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]; exact hα
  have hfmonic : (X ^ (p - 1) + C (p : ℚ_[p])).Monic := monic_X_pow_add_C _ hp0
  have hminpoly : X ^ (p - 1) + C (p : ℚ_[p]) = minpoly ℚ_[p] α :=
    minpoly.eq_of_irreducible_of_monic hirr_Qp haeval hfmonic
  have hα_int : IsIntegral ℚ_[p] α := ⟨_, hfmonic, by
    simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_C]; exact hα⟩

  have hadj_rank : Module.finrank ℚ_[p]
      ↥(IntermediateField.adjoin ℚ_[p] ({α} : Set L)) = p - 1 := by
    rw [IntermediateField.adjoin.finrank hα_int, ← hminpoly, natDegree_X_pow_add_C]
  have hL_rank : Module.finrank ℚ_[p] L = p - 1 := by
    rw [IsCyclotomicExtension.finrank L (cyclotomic_prime_irreducible_padic p),
        Nat.totient_prime hprime]

  have htop : IntermediateField.adjoin ℚ_[p] ({α} : Set L) = ⊤ := by
    rw [IntermediateField.finrank_eq_one_iff_eq_top.symm]
    have htower := Module.finrank_mul_finrank ℚ_[p]
      ↥(IntermediateField.adjoin ℚ_[p] ({α} : Set L)) L
    rw [hadj_rank, hL_rank] at htower
    exact mul_left_cancel₀ hp0 (by rw [mul_one]; exact htower)

  exact Algebra.adjoin_eq_top_of_primitive_element hα_int.isAlgebraic htop







theorem cor_10_17_tame_decomp_with_input (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [IsCyclicExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (_ℓ : ℕ) (_hℓ : Nat.Prime _ℓ) (_hℓp : _ℓ ≠ p) (_r : ℕ)
    (_hdeg : Module.finrank ℚ_[p] K = _ℓ ^ _r)


    (htame_decomp : ∃ (e : ℕ), e ∣ (p - 1) ∧
      ∀ (q : ℕ) (_ : q ≥ 1) (M : Type) (_ : Field M) (_ : Algebra ℚ_[p] M),
        IsCyclotomicExtension {q} ℚ_[p] M →
        ∃ (n : ℕ) (_ : n ≥ 1) (N : Type) (_ : Field N) (_ : Algebra ℚ_[p] N),
          IsCyclotomicExtension {n} ℚ_[p] N ∧ Nonempty (K →ₐ[ℚ_[p]] N))


    (htot_ram_cyc : ∀ (e : ℕ), e ∣ (p - 1) →
      ∃ (q : ℕ), q ≥ 1 ∧
        ∃ (M : Type) (_ : Field M) (_ : Algebra ℚ_[p] M),
          IsCyclotomicExtension {q} ℚ_[p] M) :
    LiesInCyclotomicExtension ℚ_[p] K := by


  obtain ⟨e, he_dvd, hcomp⟩ := htame_decomp


  obtain ⟨q, hq, M, hFM, hAM, hcycM⟩ := htot_ram_cyc e he_dvd

  obtain ⟨n, hn, N, hFN, hAN, hcycN, hemb⟩ := hcomp q hq M hFM hAM hcycM
  refine ⟨n, hn, ?_⟩
  letI := hFN; letI := hAN; letI := hcycN
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero ((n : ℕ) : ℚ_[p]) := inferInstance
  haveI : IsCyclotomicExtension {n} ℚ_[p] (CyclotomicField n ℚ_[p]) :=
    CyclotomicField.isCyclotomicExtension n ℚ_[p]
  obtain ⟨f⟩ := hemb
  exact ⟨(IsCyclotomicExtension.algEquiv {n} ℚ_[p] N _).toAlgHom.comp f⟩

theorem lemma_20_5_consequence (p : ℕ) [Fact (Nat.Prime p)]
    (hlem205 : ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[p] L),
      IsCyclotomicExtension {p} ℚ_[p] L ∧ Module.finrank ℚ_[p] L = p - 1)
    (_e : ℕ) (_he : _e ∣ (p - 1)) :
    ∃ (q : ℕ), q ≥ 1 ∧
      ∃ (M : Type) (_ : Field M) (_ : Algebra ℚ_[p] M),
        IsCyclotomicExtension {q} ℚ_[p] M := by


  obtain ⟨L, hF, hA, hcyc, _⟩ := hlem205
  exact ⟨p, Nat.Prime.one_le (Fact.out), L, hF, hA, hcyc⟩




noncomputable def projToLastTwo (p : ℕ) :
    Multiplicative (ZMod p × ZMod p × ZMod p) →* Multiplicative (ZMod p × ZMod p) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x).2
  map_one' := by simp [toAdd_one]
  map_mul' := by intro a b; simp [toAdd_mul, ofAdd_add]

theorem projToLastTwo_surjective (p : ℕ) : Function.Surjective (projToLastTwo p) := by
  intro y
  exact ⟨Multiplicative.ofAdd (0, Multiplicative.toAdd y), by simp [projToLastTwo, ofAdd_toAdd]⟩

theorem inertia_decomp_ZpZ3 (p : ℕ) [Fact (Nat.Prime p)]
    (_hp : p ≠ 2)
    (K : Type) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (φ : (K ≃ₐ[ℚ_[p]] K) ≃* Multiplicative (ZMod p × ZMod p × ZMod p)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[p] L)
      (_ : FiniteDimensional ℚ_[p] L) (_ : IsGalois ℚ_[p] L),
      (Module.finrank ℚ_[p] L > 1) ∧ (p ∣ Module.finrank ℚ_[p] L) ∧
      Nonempty ((L ≃ₐ[ℚ_[p]] L) ≃* Multiplicative (ZMod p × ZMod p)) := by

  set f := (projToLastTwo p).comp φ.toMonoidHom with hf_def
  set H := f.ker with hH_def

  set L := IntermediateField.fixedField H

  have hsurj : Function.Surjective f := by
    intro y; obtain ⟨z, hz⟩ := projToLastTwo_surjective p y
    exact ⟨φ.symm z, by simp [hf_def, hz]⟩


  have galIso : (↥L ≃ₐ[ℚ_[p]] ↥L) ≃* Multiplicative (ZMod p × ZMod p) :=
    (IsGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

  have hcard : Nat.card (↥L ≃ₐ[ℚ_[p]] ↥L) = p * p := by
    rw [Nat.card_congr galIso.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod, ZMod.card]

  have hfr : Module.finrank ℚ_[p] ↥L = p * p := by
    rw [← IsGalois.card_aut_eq_finrank ℚ_[p] ↥L, hcard]
  refine ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ⟨galIso⟩⟩
  ·
    rw [hfr]; nlinarith [(Fact.out : Nat.Prime p).two_le]
  ·
    rw [hfr]; exact dvd_mul_right p p

theorem ZMod_square_not_cyclic (p : ℕ) [Fact (Nat.Prime p)] :
    ¬ IsCyclic (Multiplicative (ZMod p × ZMod p)) := by
  have hp_prime := (Fact.out : Nat.Prime p)
  intro ⟨⟨g, hg⟩⟩
  have hgp : ∀ (x : Multiplicative (ZMod p × ZMod p)), x ^ p = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
    all_goals { rw [nsmul_eq_mul]; simp }
  have hord_dvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hgp g)
  have hcard : Nat.card (Multiplicative (ZMod p × ZMod p)) = p ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_multiplicative, Fintype.card_prod, ZMod.card p]
    ring
  have hcard_eq : Nat.card (Multiplicative (ZMod p × ZMod p)) = orderOf g :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  rw [hcard] at hcard_eq
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd (Nat.Prime.pos hp_prime) (hcard_eq ▸ hord_dvd)
  nlinarith [hp_prime.two_le]
















lemma index_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).index = H.index := by
  apply Subgroup.index_map_eq
  · exact φ.surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (hx.trans (map_one φ).symm)
    rw [this]; exact H.one_mem

lemma index_subgroups_card_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n} =
      Nat.card {H : Subgroup G' // H.index = n} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · intro h
    change (φ.mapSubgroup H).index = n
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl]
    rw [index_map_mulEquiv]; exact h
  · intro h
    have : (φ.mapSubgroup H).index = n := h
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl] at this
    rw [index_map_mulEquiv] at this; exact this




noncomputable def galoisCorrespondenceIndex (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (n : ℕ) :
    {H : Subgroup (K ≃ₐ[F] K) // H.index = n} ≃
    {L : IntermediateField F K // Module.finrank F L = n} where
  toFun := fun ⟨H, hH⟩ => ⟨IntermediateField.fixedField H, by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _]
    exact hH⟩
  invFun := fun ⟨L, hL⟩ => ⟨L.fixingSubgroup, by
    rwa [← IntermediateField.finrank_eq_fixingSubgroup_index]⟩
  left_inv := fun ⟨H, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _
  right_inv := fun ⟨L, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact IsGalois.fixedField_fixingSubgroup L




theorem cyclic_normal_index_subgroups_card_eq_of_mulEquiv
    {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} =
    Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := by
      change (H.map φ.toMonoidHom).Normal
      exact Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
    refine ⟨?_, h_norm', ?_⟩
    · change (H.map (φ : G →* G')).index = n
      rw [Subgroup.index_map_equiv H φ]; exact h_idx
    · haveI : (H.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
      haveI := h_norm
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mp h_cyc

  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := h_norm
    haveI : (φ.mapSubgroup.toEquiv H).Normal := h_norm
    haveI : (H.map (φ : G →* G')).Normal := ‹_›
    have h_normH : H.Normal := by
      have heq : H = (H.map (φ : G →* G')).comap (φ : G →* G') := by
        ext x; constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, he⟩; exact φ.injective he ▸ hy
      rw [heq]; exact Subgroup.Normal.comap ‹(H.map (φ : G →* G')).Normal› _
    refine ⟨?_, h_normH, ?_⟩
    · change (H.map (φ : G →* G')).index = n at h_idx
      rw [Subgroup.index_map_equiv H φ] at h_idx; exact h_idx
    · haveI := h_normH
      haveI : (H.map φ.toMonoidHom).Normal := ‹(H.map (φ : G →* G')).Normal›
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mpr h_cyc



theorem galois_quotient_extension.{u₁, u₂, u₃}
    (F : Type u₁) (L : Type u₂) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (Q : Type u₃) [Group Q] [Fintype Q]
    (φ : (L ≃ₐ[F] L) →* Q) (hφ : Function.Surjective φ) :
    ∃ (E : Type u₂) (_ : Field E) (_ : Algebra F E)
      (_ : FiniteDimensional F E) (_ : IsGalois F E),
      Nonempty ((E ≃ₐ[F] E) ≃* Q) := by
  let H := φ.ker
  let E := IntermediateField.fixedField H
  haveI : Subgroup.Normal H := φ.normal_ker
  haveI : IsGalois F E := IsGalois.of_fixedField_normal_subgroup H
  have iso1 : (L ≃ₐ[F] L) ⧸ H ≃* (↥E ≃ₐ[F] ↥E) := IsGalois.normalAutEquivQuotient H
  have iso2 : (L ≃ₐ[F] L) ⧸ H ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨iso1.symm.trans iso2⟩⟩



lemma liesInCyclotomicExtension_of_finrank_one
    (K : Type*) [Field K] [Algebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
    (h : Module.finrank ℚ_[2] K = 1) :
    LiesInCyclotomicExtension ℚ_[2] K := by
  have hbt := IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr h
  exact ⟨1, le_refl 1,
    ⟨(Algebra.ofId ℚ_[2] (CyclotomicField 1 ℚ_[2])).comp
      ((IntermediateField.botEquiv ℚ_[2] K).toAlgHom.comp
        ((IntermediateField.equivOfEq hbt.symm).toAlgHom.comp
          IntermediateField.topEquiv.symm.toAlgHom))⟩⟩


theorem surjective_of_toMultiplicative {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidHom.toMultiplicative f) := by
  intro y
  obtain ⟨x, hx⟩ := hf (Multiplicative.toAdd y)
  exact ⟨Multiplicative.ofAdd x, by simp [AddMonoidHom.toMultiplicative, hx]⟩

theorem surjective_prodMap_addMonoidHom {A B C D : Type*}
    [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] [AddZeroClass D]
    (f : A →+ C) (g : B →+ D)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (AddMonoidHom.prodMap f g) := by
  intro ⟨c, d⟩
  obtain ⟨a, ha⟩ := hf c
  obtain ⟨b, hb⟩ := hg d
  exact ⟨(a, b), Prod.ext ha hb⟩









lemma finrank_fixedField_mul_card (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (H : Subgroup (K ≃ₐ[F] K)) :
    Module.finrank F ↥(IntermediateField.fixedField H) * Nat.card H =
      Module.finrank F K := by
  have h1 := Module.finrank_mul_finrank F ↥(IntermediateField.fixedField H) K
  have h2 := IntermediateField.finrank_fixedField_eq_card (F := F) (E := K) H
  rw [← h2]; exact h1


lemma finrank_fixedField_lt (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (H : Subgroup (K ≃ₐ[F] K)) (hH : 1 < Nat.card H) :
    Module.finrank F ↥(IntermediateField.fixedField H) < Module.finrank F K := by
  have hmul := finrank_fixedField_mul_card F K H
  have hfr_pos : 0 < Module.finrank F ↥(IntermediateField.fixedField H) :=
    Module.finrank_pos
  nlinarith


lemma fixedField_isAbelianExtension (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hcomm : ∀ σ τ : (K ≃ₐ[F] K), σ * τ = τ * σ)
    (H : Subgroup (K ≃ₐ[F] K)) [H.Normal] :
    IsAbelianExtension F ↥(IntermediateField.fixedField H) where
  isGalois := inferInstance
  comm := by
    intro σ τ
    let e := IsGalois.normalAutEquivQuotient H
    obtain ⟨s, rfl⟩ := e.surjective σ
    obtain ⟨t, rfl⟩ := e.surjective τ
    rw [← e.map_mul, ← e.map_mul]
    congr 1
    revert s t; intro s t
    refine Quotient.inductionOn₂ s t ?_
    intro a b
    show (⟦a * b⟧ : (K ≃ₐ[F] K) ⧸ H) = ⟦b * a⟧
    congr 1; exact hcomm a b


set_option maxHeartbeats 1600000 in
lemma fixedField_sup_of_inf_bot (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (H₁ H₂ : Subgroup (K ≃ₐ[F] K)) (h : H₁ ⊓ H₂ = ⊥) :
    IntermediateField.fixedField H₁ ⊔ IntermediateField.fixedField H₂ = ⊤ := by
  have key : IntermediateField.fixedField (H₁ ⊓ H₂) =
      IntermediateField.fixedField H₁ ⊔ IntermediateField.fixedField H₂ := by
    let e := IsGalois.intermediateFieldEquivSubgroup (F := F) (E := K)
    apply e.injective
    rw [e.map_sup]
    simp only [show e = IsGalois.intermediateFieldEquivSubgroup from rfl,
      IsGalois.intermediateFieldEquivSubgroup_apply,
      IntermediateField.fixingSubgroup_fixedField]
    rfl
  rw [h] at key; rw [← key]; exact IntermediateField.fixedField_bot











noncomputable def adicCompletionTensorLift
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K L (𝔮.adicCompletion L)] :
    TensorProduct K (𝔭.adicCompletion K) L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (𝔭.adicCompletion K) (𝔮.adicCompletion L))
    (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L))
    (fun _ _ => mul_comm _ _)







set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


section
set_option synthInstance.maxHeartbeats 400000
theorem adicCompletionIntegers_scalarTower
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    letI : Algebra (↥(𝔭.adicCompletionIntegers K)) (𝔮.adicCompletion L) :=
      RingHom.toAlgebra ((algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)).comp
        (algebraMap (↥(𝔭.adicCompletionIntegers K)) (𝔭.adicCompletion K)))
    IsScalarTower (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))
      (𝔮.adicCompletion L) := by
  letI : Algebra (↥(𝔭.adicCompletionIntegers K)) (𝔮.adicCompletion L) :=
    RingHom.toAlgebra ((algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)).comp
      (algebraMap (↥(𝔭.adicCompletionIntegers K)) (𝔭.adicCompletion K)))
  exact IsScalarTower.of_algebraMap_eq (fun x => (h_compat x).symm)
end


lemma withZero_mul_eq_exp_neg_one_aux {x y : WithZero (Multiplicative ℤ)}
    (hprod : x * y = WithZero.exp (-1))
    (hx : x ≤ 1) (hy : y ≤ 1) :
    x = 1 ∨ y = 1 := by
  have hne : x * y ≠ 0 := by rw [hprod]; exact WithZero.coe_ne_zero
  lift x to Multiplicative ℤ using left_ne_zero_of_mul hne
  lift y to Multiplicative ℤ using right_ne_zero_of_mul hne
  simp only [WithZero.coe_le_one, ← WithZero.coe_mul, WithZero.coe_inj, WithZero.exp] at *
  have hn : Multiplicative.toAdd x ≤ 0 := by
    rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl,
        show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl,
        Multiplicative.ofAdd_le] at hx; exact hx
  have hm : Multiplicative.toAdd y ≤ 0 := by
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl,
        show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl,
        Multiplicative.ofAdd_le] at hy; exact hy
  have hnm : Multiplicative.toAdd x + Multiplicative.toAdd y = -1 := by
    rw [← toAdd_mul, hprod]; rfl
  rcases eq_or_ne (Multiplicative.toAdd x) 0 with h | h
  · left; exact_mod_cast show x = (1 : Multiplicative ℤ) by
      change Multiplicative.ofAdd (Multiplicative.toAdd x) = Multiplicative.ofAdd 0; rw [h]
  · right; have hm0 : Multiplicative.toAdd y = 0 := by omega
    exact_mod_cast show y = (1 : Multiplicative ℤ) by
      change Multiplicative.ofAdd (Multiplicative.toAdd y) = Multiplicative.ofAdd 0; rw [hm0]

open IsDedekindDomain.HeightOneSpectrum in

set_option maxHeartbeats 800000 in
theorem prop_8_11_map_asIdeal_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    Ideal.map (algebraMap A (𝔭.adicCompletionIntegers K)) 𝔭.asIdeal =
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by

  have valued_eq : ∀ r : A, (Valued.v : Valuation (𝔭.adicCompletion K) _)
      ((algebraMap A (𝔭.adicCompletionIntegers K) r) : 𝔭.adicCompletion K) =
      𝔭.intValuation r := fun r => by
    simp [algebraMap_adicCompletionIntegers_apply, Valued.valuedCompletion_apply,
          valuation_of_algebraMap]

  obtain ⟨π, hπ⟩ := intValuation_exists_uniformizer 𝔭

  have hπ_mem : π ∈ 𝔭.asIdeal := by
    rw [← intValuation_lt_one_iff_mem, hπ]
    unfold WithZero.exp
    rw [show (1 : WithZero (Multiplicative ℤ)) = ↑(1 : Multiplicative ℤ) from rfl,
        WithZero.coe_lt_coe]
    show Multiplicative.ofAdd (-1 : ℤ) < Multiplicative.ofAdd (0 : ℤ)
    exact Multiplicative.ofAdd_lt.mpr (by norm_num)

  have hirr : Irreducible (algebraMap A (𝔭.adicCompletionIntegers K) π) := by
    constructor
    ·
      rw [adicCompletionIntegers.isUnit_iff_valued_eq_one, valued_eq, hπ]
      intro h
      exact absurd (Multiplicative.ofAdd.injective (WithZero.coe_injective h))
        (show (-1 : ℤ) ≠ 0 from by norm_num)
    ·
      intro a b hab
      have hv_a := a.2; have hv_b := b.2
      have hv_prod : (Valued.v : Valuation (𝔭.adicCompletion K) _) (a : _) *
          (Valued.v : Valuation (𝔭.adicCompletion K) _) (b : _) = WithZero.exp (-1) := by
        rw [← Valuation.map_mul]
        show Valued.v ((a * b : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = _
        rw [← hab, valued_eq, hπ]
      rcases withZero_mul_eq_exp_neg_one_aux hv_prod hv_a hv_b with h | h
      · left; rwa [adicCompletionIntegers.isUnit_iff_valued_eq_one]
      · right; rwa [adicCompletionIntegers.isUnit_iff_valued_eq_one]

  have hmax := hirr.maximalIdeal_eq

  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        adicCompletionIntegers.isUnit_iff_valued_eq_one, valued_eq]
    exact ne_of_lt ((intValuation_lt_one_iff_mem 𝔭 r).mpr hr)
  ·
    rw [hmax]
    apply Ideal.span_le.mpr
    simp only [Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hπ_mem


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
theorem prop_8_11_comap_maximalIdeal_pow
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    (n : ℕ) :
    Ideal.comap (algebraMap B (𝔮.adicCompletionIntegers L))
      ((IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) ^ n) = 𝔮.asIdeal ^ n := by
  open IsDedekindDomain.HeightOneSpectrum WithZeroMulInt Valuation in
  set V : Valuation (𝔮.adicCompletion L) _ := Valued.v
  have hVsurj : Function.Surjective V := valuedAdicCompletion_surjective L 𝔮
  have hgen : (IsRankOneDiscrete.generator V : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    rw [IsRankOneDiscrete.generator_eq_neg_exp_one_of_surjective hVsurj]
    simp [Units.val_mk0]
  obtain ⟨π, hπ⟩ := V.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hInts : V.Integers (𝔮.adicCompletionIntegers L) :=
    adicCompletionIntegers.integers L 𝔮
  have hm_eq : (IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) ^ n =
      Ideal.span {⟨↑π, π.2⟩ ^ n} :=
    pow_Uniformizer_is_pow_generator (Uniformizer.mk' hπ) n
  have hVπn : V ((↑π : 𝔮.adicCompletion L) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, hgen, ← WithZero.exp_nsmul, smul_neg, nsmul_one]
  ext b
  rw [Ideal.mem_comap, hm_eq, Ideal.mem_span_singleton, ← intValuation_le_pow_iff_mem,
      hInts.dvd_iff_le, map_pow]
  simp only [show (algebraMap (↥(𝔮.adicCompletionIntegers L)) (𝔮.adicCompletion L))
      ((algebraMap B (↥(𝔮.adicCompletionIntegers L))) b) =
    (algebraMap B L b : 𝔮.adicCompletion L) from rfl,
    show (algebraMap (↥(𝔮.adicCompletionIntegers L)) (𝔮.adicCompletion L))
      ⟨↑π, π.2⟩ = (↑π : 𝔮.adicCompletion L) from rfl]
  rw [valuedAdicCompletion_eq_valuation' 𝔮 (algebraMap B L b), valuation_of_algebraMap, hVπn]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem prop_8_11_ideal_power_completion_iff
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    (n : ℕ) :
    Ideal.map (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≤
      (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ^ n ↔
    Ideal.map (algebraMap A B) 𝔭.asIdeal ≤ 𝔮.asIdeal ^ n := by
  rw [← prop_8_11_map_asIdeal_eq_maximalIdeal (K := K) 𝔭, Ideal.map_map,
      show (algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))).comp
        (algebraMap A (↥(𝔭.adicCompletionIntegers K))) =
        algebraMap A (↥(𝔮.adicCompletionIntegers L)) from
        (IsScalarTower.algebraMap_eq A (↥(𝔭.adicCompletionIntegers K))
          (↥(𝔮.adicCompletionIntegers L))).symm,
      show algebraMap A (↥(𝔮.adicCompletionIntegers L)) =
        (algebraMap B (↥(𝔮.adicCompletionIntegers L))).comp (algebraMap A B) from
        IsScalarTower.algebraMap_eq A B (↥(𝔮.adicCompletionIntegers L)),
      ← Ideal.map_map, Ideal.map_le_iff_le_comap,
      prop_8_11_comap_maximalIdeal_pow (L := L) 𝔮 n]

theorem ch8_10_ramificationIdx_eq_aux
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)] :
    Ideal.ramificationIdx
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) =
    Ideal.ramificationIdx 𝔭.asIdeal 𝔮.asIdeal := by
  show sSup {n | _} = sSup {n | _}
  congr 1
  ext n
  exact prop_8_11_ideal_power_completion_iff 𝔭 𝔮 n

theorem adicCompletionIntegers_algebraMap_injective
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    Function.Injective (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L)) := by
  intro x y hxy
  have hx := h_compat x
  have hy := h_compat y
  have hval : (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val =
              (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) y.val := by
    rw [← hx, ← hy]; exact congrArg Subtype.val hxy
  exact Subtype.ext ((algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)).injective hval)

theorem ch8_10_map_maximalIdeal_ne_bot
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    Ideal.map (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≠ ⊥ := by
  haveI : Module.IsTorsionFree (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (adicCompletionIntegers_algebraMap_injective 𝔭 𝔮 h_compat)
  exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field _)

theorem ch8_10_map_asIdeal_ne_bot
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    (h_inj : Function.Injective (algebraMap A B)) :
    Ideal.map (algebraMap A B) 𝔭.asIdeal ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective h_inj]
  exact 𝔭.ne_bot

theorem ch8_10_bddAbove_completion_aux
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    BddAbove {n | Ideal.map
      (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≤
      (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ^ n} := by
  have hne : Ideal.map (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≠ ⊥ :=
    ch8_10_map_maximalIdeal_ne_bot (K := K) (L := L) 𝔭 𝔮 h_compat

  have hM : (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ≠ ⊤ :=
    Ideal.IsPrime.ne_top'
  by_contra h_not_bdd
  rw [not_bddAbove_iff] at h_not_bdd
  have hle : Ideal.map (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≤
      ⨅ n, (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ^ n := by
    rw [le_iInf_iff]
    intro n
    obtain ⟨m, hm, hmn⟩ := h_not_bdd n
    exact hm.trans (Ideal.pow_le_pow_right (by omega))
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hM] at hle
  exact hne (le_bot_iff.mp hle)

theorem ch8_10_bddAbove_original_aux
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    (h_inj : Function.Injective (algebraMap A B)) :
    BddAbove {n | Ideal.map (algebraMap A B) 𝔭.asIdeal ≤ 𝔮.asIdeal ^ n} := by
  have hne : Ideal.map (algebraMap A B) 𝔭.asIdeal ≠ ⊥ :=
    ch8_10_map_asIdeal_ne_bot (K := K) (L := L) 𝔭 𝔮 h_inj
  have hQ : 𝔮.asIdeal ≠ ⊤ := 𝔮.isPrime.ne_top
  by_contra h_not_bdd
  rw [not_bddAbove_iff] at h_not_bdd
  have hle : Ideal.map (algebraMap A B) 𝔭.asIdeal ≤ ⨅ n, 𝔮.asIdeal ^ n := by
    rw [le_iInf_iff]
    intro n
    obtain ⟨m, hm, hmn⟩ := h_not_bdd n
    exact hm.trans (Ideal.pow_le_pow_right (by omega))
  rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hQ] at hle
  exact hne (le_bot_iff.mp hle)

theorem ch8_10_completion_ramificationIdx_eq
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val)
    (h_inj : Function.Injective (algebraMap A B)) :

    Ideal.ramificationIdx
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) =
    Ideal.ramificationIdx 𝔭.asIdeal 𝔮.asIdeal ∧
    BddAbove {n | Ideal.map
      (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≤
      (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ^ n} ∧
    BddAbove {n | Ideal.map (algebraMap A B) 𝔭.asIdeal ≤ 𝔮.asIdeal ^ n} := by
  exact ⟨ch8_10_ramificationIdx_eq_aux (K := K) (L := L) 𝔭 𝔮,
    ch8_10_bddAbove_completion_aux (K := K) (L := L) 𝔭 𝔮 h_compat,
    ch8_10_bddAbove_original_aux (K := K) (L := L) 𝔭 𝔮 h_inj⟩

set_option synthInstance.maxHeartbeats 400000 in
lemma completion_ideal_power_iff
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val)
    (h_inj : Function.Injective (algebraMap A B))
    (n : ℕ) :

    Ideal.map (algebraMap ↥(𝔭.adicCompletionIntegers K) ↥(𝔮.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≤
      (IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) ^ n ↔
    Ideal.map (algebraMap A B) 𝔭.asIdeal ≤ 𝔮.asIdeal ^ n := by
  obtain ⟨h_eq, h_bdd₁, h_bdd₂⟩ := ch8_10_completion_ramificationIdx_eq 𝔭 𝔮 (K := K) (L := L) h_compat h_inj

  constructor
  · intro h
    exact Ideal.le_pow_of_le_ramificationIdx (h_eq ▸ le_csSup h_bdd₁ h)
  · intro h
    exact Ideal.le_pow_of_le_ramificationIdx (h_eq.symm ▸ le_csSup h_bdd₂ h)

universe u_A₆ u_K₆ u_L₆ u_B₆ in
open IsDedekindDomain in
theorem part_3a_ramification_idx_preserved
    (A : Type u_A₆) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₆) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L₆) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B₆) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)).ramificationIdx
      (IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) =
      𝔭.asIdeal.ramificationIdx 𝔮.asIdeal := by
  have h_inj_AB : Function.Injective (algebraMap A B) := by
    have hinj_AL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L] at hinj_AL
    exact Function.Injective.of_comp (f := algebraMap B L) (RingHom.coe_comp _ _ ▸ hinj_AL)

  show sSup {n | _} = sSup {n | _}
  congr 1
  ext n
  exact completion_ideal_power_iff 𝔭 𝔮 h_compat h_inj_AB n

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
universe u_A₇ u_K₇ u_L₇ u_B₇ in
open IsDedekindDomain in
theorem completion_maximalIdeal_comap
    (A : Type u_A₇) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₇) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L₇) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B₇) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :
    Ideal.comap (algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L)))
      (IsLocalRing.maximalIdeal (↥(𝔮.adicCompletionIntegers L))) =
      IsLocalRing.maximalIdeal (↥(𝔭.adicCompletionIntegers K)) := by
  have h_inj_AB : Function.Injective (algebraMap A B) := by
    have hinj_AL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L] at hinj_AL
    exact Function.Injective.of_comp (f := algebraMap B L) (RingHom.coe_comp _ _ ▸ hinj_AL)

  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L)))).out 2 4).mp


  rw [show IsLocalRing.maximalIdeal (↥(𝔮.adicCompletionIntegers L)) =
    (IsLocalRing.maximalIdeal (↥(𝔮.adicCompletionIntegers L))) ^ 1 from (pow_one _).symm]
  rw [completion_ideal_power_iff 𝔭 𝔮 h_compat h_inj_AB 1]

  rw [pow_one]
  exact Ideal.map_le_iff_le_comap.mpr h𝔮_over_𝔭

set_option synthInstance.maxHeartbeats 400000 in
open IsDedekindDomain in
universe u_A₈' u_K₈' in
noncomputable def completion_residueFieldEquiv
    (A : Type u_A₈') [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₈') [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔭 : HeightOneSpectrum A) :
    (↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≃+*
    (A ⧸ 𝔭.asIdeal) :=
  (RingHom.quotientKerEquivOfSurjective
    (𝔭.surj_completionResidueMap (K := K))).symm.trans
    (Ideal.quotEquivOfEq (𝔭.ker_completionResidueMap (K := K)))

set_option synthInstance.maxHeartbeats 400000 in
universe u_A₈c u_K₈c u_L₈c u_B₈c in
open IsDedekindDomain in
theorem completion_residueFieldEquiv_compat
    (A : Type u_A₈c) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₈c) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L₈c) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B₈c) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    (hcomap_completion : Ideal.comap
      (algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L)))
      (IsLocalRing.maximalIdeal (↥(𝔮.adicCompletionIntegers L))) =
      IsLocalRing.maximalIdeal (↥(𝔭.adicCompletionIntegers K)))
    (hcomap_original : Ideal.comap (algebraMap A B) 𝔮.asIdeal = 𝔭.asIdeal) :
    RingHom.comp
      (@algebraMap (A ⧸ 𝔭.asIdeal) (B ⧸ 𝔮.asIdeal) _ _
        (Ideal.Quotient.algebraQuotientOfLEComap hcomap_original.ge))
      (completion_residueFieldEquiv A K 𝔭).toRingHom =
    RingHom.comp
      (completion_residueFieldEquiv B L 𝔮).toRingHom
      (@algebraMap
        (↥(𝔭.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K))
        (↥(𝔮.adicCompletionIntegers L) ⧸
          IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L)) _ _
        (Ideal.Quotient.algebraQuotientOfLEComap hcomap_completion.ge)) := by
  ext q
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.surj_completionResidueMap 𝔭
    (Ideal.Quotient.mk _ q)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [← ha]

  have hkey_A : (completion_residueFieldEquiv A K 𝔭) (𝔭.completionResidueMap a) =
      Ideal.Quotient.mk 𝔭.asIdeal a := by
    simp only [completion_residueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk]
  rw [hkey_A]

  have hcompat : @algebraMap
      (↥(𝔭.adicCompletionIntegers K) ⧸ IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K))
      (↥(𝔮.adicCompletionIntegers L) ⧸ IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L))
      _ _ (Ideal.Quotient.algebraQuotientOfLEComap hcomap_completion.ge)
      (𝔭.completionResidueMap a) =
      𝔮.completionResidueMap (algebraMap A B a) := by
    simp only [IsDedekindDomain.HeightOneSpectrum.completionResidueMap, RingHom.comp_apply]
    change Ideal.quotientMap _ (algebraMap _ _) hcomap_completion.ge
        (Ideal.Quotient.mk _ ((algebraMap A (↥(𝔭.adicCompletionIntegers K))) a)) =
      Ideal.Quotient.mk _ ((algebraMap B (↥(𝔮.adicCompletionIntegers L))) ((algebraMap A B) a))
    rw [Ideal.quotientMap_mk]
    congr 1
    rw [← IsScalarTower.algebraMap_apply A (↥(𝔭.adicCompletionIntegers K))
          (↥(𝔮.adicCompletionIntegers L)),
        ← IsScalarTower.algebraMap_apply A B (↥(𝔮.adicCompletionIntegers L))]
  rw [hcompat]

  have hkey_B : (completion_residueFieldEquiv B L 𝔮)
      (𝔮.completionResidueMap (algebraMap A B a)) =
      Ideal.Quotient.mk 𝔮.asIdeal (algebraMap A B a) := by
    simp only [completion_residueFieldEquiv, RingEquiv.trans_apply,
      RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk]
  rw [hkey_B]

  change Ideal.quotientMap _ (algebraMap A B) hcomap_original.ge
      (Ideal.Quotient.mk 𝔭.asIdeal a) =
    Ideal.Quotient.mk 𝔮.asIdeal ((algebraMap A B) a)
  rw [Ideal.quotientMap_mk]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
universe u_A₈ u_K₈ u_L₈ u_B₈ in
open IsDedekindDomain in
theorem completion_residueField_finrank_eq
    (A : Type u_A₈) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₈) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L₈) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B₈) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    (hcomap_completion : Ideal.comap
      (algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L)))
      (IsLocalRing.maximalIdeal (↥(𝔮.adicCompletionIntegers L))) =
      IsLocalRing.maximalIdeal (↥(𝔭.adicCompletionIntegers K)))
    (hcomap_original : Ideal.comap (algebraMap A B) 𝔮.asIdeal = 𝔭.asIdeal) :
    @Module.finrank
      (↥(𝔭.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K))
      (↥(𝔮.adicCompletionIntegers L) ⧸
        IsLocalRing.maximalIdeal ↥(𝔮.adicCompletionIntegers L))
      _ (inferInstance)
      (Ideal.Quotient.algebraQuotientOfLEComap hcomap_completion.ge).toModule =
    @Module.finrank (A ⧸ 𝔭.asIdeal) (B ⧸ 𝔮.asIdeal)
      _ (inferInstance)
      (Ideal.Quotient.algebraQuotientOfLEComap hcomap_original.ge).toModule :=
  @Algebra.finrank_eq_of_equiv_equiv _ _ _ _
    (Ideal.Quotient.algebraQuotientOfLEComap hcomap_completion.ge)
    _ _ _ _
    (Ideal.Quotient.algebraQuotientOfLEComap hcomap_original.ge)
    (completion_residueFieldEquiv A K 𝔭) (completion_residueFieldEquiv B L 𝔮)
    (completion_residueFieldEquiv_compat A K L B 𝔭 𝔮 h𝔮_over_𝔭 hcomap_completion hcomap_original)

universe u_A₇' u_K₇' u_L₇' u_B₇' in
open IsDedekindDomain in
theorem part_3b_inertia_deg_preserved
    (A : Type u_A₇') [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₇') [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L₇') [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B₇') [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A) (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [Algebra A (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A (𝔭.adicCompletionIntegers K) (𝔮.adicCompletionIntegers L)]
    [IsScalarTower A B (𝔮.adicCompletionIntegers L)]
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    (h_compat : ∀ x : ↥(𝔭.adicCompletionIntegers K),
      ((algebraMap (↥(𝔭.adicCompletionIntegers K)) (↥(𝔮.adicCompletionIntegers L))) x).val =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)) x.val) :

    (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)).inertiaDeg
      (IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L)) =
      𝔭.asIdeal.inertiaDeg 𝔮.asIdeal := by

  unfold Ideal.inertiaDeg


  have hRHS : Ideal.comap (algebraMap A B) 𝔮.asIdeal = 𝔭.asIdeal := by
    have hne_top : Ideal.comap (algebraMap A B) 𝔮.asIdeal ≠ ⊤ := by
      intro heq
      exact 𝔮.isPrime.ne_top (Ideal.comap_eq_top_iff.mp heq)
    exact (𝔭.isPrime.isMaximal 𝔭.ne_bot).eq_of_le hne_top h𝔮_over_𝔭 |>.symm
  rw [dif_pos hRHS]

  have hLHS := completion_maximalIdeal_comap A K L B 𝔭 𝔮 h𝔮_over_𝔭 h_compat

  rw [dif_pos hLHS]

  exact completion_residueField_finrank_eq A K L B 𝔭 𝔮 h𝔮_over_𝔭 hLHS hRHS


set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1600000 in
universe u_A u_K u_L u_B in
open IsDedekindDomain in

theorem isGalois_adicCompletion
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal]
    (hgal : IsGalois K L) :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
  letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭


  haveI : (Valued.v : Valuation (𝔭.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF : NontriviallyNormedField (𝔭.adicCompletion K) :=
    Valued.toNontriviallyNormedField (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))

  haveI : (Valued.v : Valuation (𝔮.adicCompletion L)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF_L : NontriviallyNormedField (𝔮.adicCompletion L) :=
    Valued.toNontriviallyNormedField (𝔮.adicCompletion L) (WithZero (Multiplicative ℤ))

  haveI : ContinuousSMul (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭)
    exact UniformSpace.Completion.continuous_extension

  haveI := isScalarTower_adicCompletion (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  let Φ := (Algebra.TensorProduct.lift
      (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
      (Algebra.algHom K L (𝔮.adicCompletion L))
      (fun x y => mul_comm _ _)).toLinearMap
  have h_dense : DenseRange Φ := by
    apply Dense.mono _ (𝔮.denseRange_algebraMap L)
    intro a ⟨l, hl⟩
    exact ⟨1 ⊗ₜ[K] l, by simp [Φ, Algebra.algHom, hl]⟩
  have h_closed : IsClosed (Φ.range : Set (𝔮.adicCompletion L)) :=
    Submodule.closed_of_finiteDimensional Φ.range
  have h_surj : Function.Surjective Φ := by
    rw [← Set.range_eq_univ, ← LinearMap.coe_range,
      ← h_closed.closure_eq]
    exact h_dense.closure_range

  haveI hfd : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
    Module.Finite.of_surjective Φ h_surj


  have hadjoin_top : Algebra.adjoin (𝔭.adicCompletion K)
      (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by

    let Φ_alg := Algebra.TensorProduct.lift
        (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
        (Algebra.algHom K L (𝔮.adicCompletion L))
        (fun _ _ => mul_comm _ _)
    have h_surj_alg : Function.Surjective Φ_alg := h_surj
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := h_surj_alg x
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [map_zero]; exact Subalgebra.zero_mem _
    · intro k l
      show Φ_alg (k ⊗ₜ[K] l) ∈ Algebra.adjoin (𝔭.adicCompletion K)
          (Set.range (algebraMap L (𝔮.adicCompletion L)))
      simp only [Φ_alg, Algebra.TensorProduct.lift_tmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k)
        (Algebra.subset_adjoin ⟨l, rfl⟩)
    · exact fun a b ha hb => (map_add Φ_alg a b) ▸ Subalgebra.add_mem _ ha hb


  classical
  obtain ⟨p, hsep, hsplit⟩ := (IsGalois.tfae.out 0 3).mp hgal
  set_option maxHeartbeats 800000 in
  haveI : Polynomial.IsSplittingField (𝔭.adicCompletion K) (𝔮.adicCompletion L)
      (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p) := {
    splits' := by
      rw [Polynomial.map_map]
      have h1 := hsplit.splits'.map (algebraMap L (𝔮.adicCompletion L))
      rwa [Polynomial.map_map, show (algebraMap L (𝔮.adicCompletion L)).comp (algebraMap K L) =
        (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion L)).comp
          (algebraMap K (𝔭.adicCompletion K)) from by
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]] at h1

    adjoin_rootSet' := by
      rw [eq_top_iff, ← hadjoin_top]
      apply Algebra.adjoin_le
      intro x ⟨l, hl⟩; subst hl
      have hmem : l ∈ Algebra.adjoin K (p.rootSet L) :=
        hsplit.adjoin_rootSet' ▸ Algebra.mem_top
      have h1 : (algebraMap L (𝔮.adicCompletion L)) l ∈
          Subalgebra.map (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L))
            (Algebra.adjoin K (p.rootSet L)) := ⟨l, hmem, rfl⟩
      rw [AlgHom.map_adjoin] at h1
      have h2 : Algebra.adjoin K
          ((IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L)) ≤
          (Algebra.adjoin (𝔭.adicCompletion K)
            ((IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L))).restrictScalars K := by
        apply Algebra.adjoin_le
        intro x hx; show x ∈ Algebra.adjoin (𝔭.adicCompletion K) _
        exact Algebra.subset_adjoin hx
      have h3 := h2 h1
      have himg : (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L)) '' (p.rootSet L) ⊆
          (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p).rootSet (𝔮.adicCompletion L) := by
        intro y ⟨r, hr, hry⟩; subst hry
        simp only [Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hr ⊢
        rw [Polynomial.mem_aroots] at hr ⊢
        refine ⟨Polynomial.map_ne_zero_iff (algebraMap K (𝔭.adicCompletion K)).injective |>.mpr hr.1, ?_⟩
        simp only [IsScalarTower.toAlgHom_apply, Polynomial.aeval_map_algebraMap,
                   Polynomial.aeval_algebraMap_apply (𝔮.adicCompletion L) r p, hr.2, map_zero]
      exact Algebra.adjoin_mono himg h3
  }
  exact @IsGalois.of_separable_splitting_field (𝔭.adicCompletion K) _ (𝔮.adicCompletion L) _ _
    (Polynomial.map (algebraMap K (𝔭.adicCompletion K)) p) this (hsep.map)

universe u_A u_K u_L u_B in
open IsDedekindDomain in
theorem adjoin_range_algebraMap_adicCompletion_eq_top
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal] :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    Algebra.adjoin (𝔭.adicCompletion K)
      (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by
  letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  haveI : (Valued.v : Valuation (𝔭.adicCompletion K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF : NontriviallyNormedField (𝔭.adicCompletion K) :=
    Valued.toNontriviallyNormedField (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))

  haveI : (Valued.v : Valuation (𝔮.adicCompletion L)
      (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne Valued.v (e := 2) (by norm_num)
  letI instNNF_L : NontriviallyNormedField (𝔮.adicCompletion L) :=
    Valued.toNontriviallyNormedField (𝔮.adicCompletion L) (WithZero (Multiplicative ℤ))

  haveI : ContinuousSMul (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭)
    exact UniformSpace.Completion.continuous_extension

  haveI := isScalarTower_adicCompletion (L := L) K 𝔭 𝔮 h𝔮_over_𝔭

  haveI hfd : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by
    let Φ := (Algebra.TensorProduct.lift
        (Algebra.algHom (𝔭.adicCompletion K) (𝔭.adicCompletion K) (𝔮.adicCompletion L))
        (Algebra.algHom K L (𝔮.adicCompletion L))
        (fun x y => mul_comm _ _)).toLinearMap
    have h_dense : DenseRange Φ := by
      apply Dense.mono _ (𝔮.denseRange_algebraMap L)
      intro a ⟨l, hl⟩
      exact ⟨1 ⊗ₜ[K] l, by simp [Φ, Algebra.algHom, hl]⟩
    have h_closed : IsClosed (Φ.range : Set (𝔮.adicCompletion L)) :=
      Submodule.closed_of_finiteDimensional Φ.range
    have h_surj : Function.Surjective Φ := by
      rw [← Set.range_eq_univ, ← LinearMap.coe_range,
        ← h_closed.closure_eq]
      exact h_dense.closure_range
    exact Module.Finite.of_surjective Φ h_surj

  set S := Algebra.adjoin (𝔭.adicCompletion K)
    (Set.range (algebraMap L (𝔮.adicCompletion L))) with hS_def

  haveI : FiniteDimensional (𝔭.adicCompletion K) S.toSubmodule :=
    Submodule.finiteDimensional_of_le le_top

  have hS_closed : IsClosed (S.toSubmodule : Set (𝔮.adicCompletion L)) :=
    Submodule.closed_of_finiteDimensional S.toSubmodule

  have hS_carrier : (S : Set (𝔮.adicCompletion L)) = (S.toSubmodule : Set (𝔮.adicCompletion L)) :=
    rfl

  have hS_closed' : IsClosed (S : Set (𝔮.adicCompletion L)) :=
    hS_carrier ▸ hS_closed

  have h_range_sub : Set.range (algebraMap L (𝔮.adicCompletion L)) ⊆ ↑S :=
    Algebra.subset_adjoin

  have h_dense : Dense (Set.range (algebraMap L (𝔮.adicCompletion L))) :=
    𝔮.denseRange_algebraMap L

  have hS_dense : Dense (S : Set (𝔮.adicCompletion L)) :=
    h_dense.mono h_range_sub

  have hS_eq_univ : (S : Set (𝔮.adicCompletion L)) = Set.univ := by
    rw [← hS_closed'.closure_eq, hS_dense.closure_eq]
  rw [SetLike.ext'_iff]
  simp [hS_eq_univ]

universe u_A u_K u_L u_B in
open IsDedekindDomain in
theorem thm_11_23_part6_galois_implication
    (A : Type u_A) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type u_L) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type u_B) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [IsFractionRing B L]
    [𝔮.asIdeal.LiesOver 𝔭.asIdeal]
    (hgal : IsGalois K L) :
    letI := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭
    IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) ∧
    ∃ (φ : (𝔮.adicCompletion L ≃ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) →*
          (L ≃ₐ[K] L)),
      Function.Injective φ := by
  letI inst_alg := instAlgebraAdicCompletionOfLiesOver (L := L) K 𝔭 𝔮 h𝔮_over_𝔭


  have hIsGalois : IsGalois (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by


    exact isGalois_adicCompletion A K L B 𝔭 𝔮 h𝔮_over_𝔭 hgal


  have hInj : ∃ (φ : (𝔮.adicCompletion L ≃ₐ[𝔭.adicCompletion K]
        𝔮.adicCompletion L) →* (L ≃ₐ[K] L)),
      Function.Injective φ := by

    haveI h_sc : IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
      isScalarTower_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭
    haveI h_sc2 : IsScalarTower K L (𝔮.adicCompletion L) := inferInstance
    have h_gen : Algebra.adjoin (𝔭.adicCompletion K)
        (Set.range (algebraMap L (𝔮.adicCompletion L))) = ⊤ := by
      exact adjoin_range_algebraMap_adicCompletion_eq_top A K L B 𝔭 𝔮 h𝔮_over_𝔭
    haveI : Normal K L := IsGalois.to_normal

    refine ⟨(AlgEquiv.restrictNormalHom (F := K) (K₁ := 𝔮.adicCompletion L) L).comp
      ⟨⟨fun σ => AlgEquiv.restrictScalars K σ, rfl⟩, fun _ _ => rfl⟩, ?_⟩

    intro σ τ hστ
    simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk] at hστ

    have h_eq : ∀ y : L, σ (algebraMap L (𝔮.adicCompletion L) y) =
        τ (algebraMap L (𝔮.adicCompletion L) y) := by
      intro y
      have h1 := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L y
      have h2 := AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L y
      rw [AlgEquiv.restrictScalars_apply] at h1 h2
      rw [← h1, ← h2]
      congr 1
      exact AlgEquiv.ext_iff.mp hστ y

    ext x
    have h_alg : ∀ y ∈ Set.range (algebraMap L (𝔮.adicCompletion L)),
        (σ.toAlgHom : 𝔮.adicCompletion L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) y =
        (τ.toAlgHom : 𝔮.adicCompletion L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L) y := by
      rintro _ ⟨y, rfl⟩
      simp only [AlgEquiv.toAlgHom_eq_coe]
      exact h_eq y
    exact AlgHom.ext_iff.mp (AlgHom.ext_of_adjoin_eq_top h_gen h_alg) x
  exact ⟨hIsGalois, hInj⟩


universe u_cse_A u_cse_K u_cse_L u_cse_B in
open IsDedekindDomain in

open IsDedekindDomain in
theorem theorem_11_23_part1_separable
    (A : Type*) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K L (𝔮.adicCompletion L)]
    [FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion L)] :
    Algebra.IsSeparable (𝔭.adicCompletion K) (𝔮.adicCompletion L) := by


  haveI : CharZero (𝔭.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective K (𝔭.adicCompletion K))

  haveI : Algebra.IsAlgebraic (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
    Algebra.IsAlgebraic.of_finite (𝔭.adicCompletion K) (𝔮.adicCompletion L)


  exact ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
open IsDedekindDomain in
theorem theorem_11_23_part2_unique_prime
    (A : Type*) [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    IsDiscreteValuationRing (𝔮.adicCompletionIntegers L) := inferInstance




















end KroneckerWeber


def theorem_11_23_part1_separable := @KroneckerWeber.theorem_11_23_part1_separable
def theorem_11_23_part2_unique_prime := @KroneckerWeber.theorem_11_23_part2_unique_prime
def thm_11_23_part6_galois_implication := @KroneckerWeber.thm_11_23_part6_galois_implication

end
