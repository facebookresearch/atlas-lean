/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Atlas.NumberTheoryI.code.Cor1015
import Atlas.NumberTheoryI.code.LocalExtensions
import Atlas.NumberTheoryI.code.TracePairing

noncomputable section

theorem dvr_extension_isLocalHom
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] :
    IsLocalHom (algebraMap A B) := by

  have hint : (algebraMap A B).IsIntegral := fun b => isIntegral_of_noetherian inferInstance b

  have hmax : ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (algebraMap A B) hint
      (IsLocalRing.maximalIdeal B)

  have hcomap : (IsLocalRing.maximalIdeal B).comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hmax

  constructor
  intro a ha
  by_contra hna

  have ha_mem : a ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]; exact mem_nonunits_iff.mpr hna
  rw [← hcomap] at ha_mem
  have hba : algebraMap A B a ∈ IsLocalRing.maximalIdeal B := Ideal.mem_comap.mp ha_mem
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hba)) ha

theorem dvr_extension_module_finite
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    Module.Finite A B :=
  IsIntegralClosure.finite A K L B

theorem dvr_extension_finite_and_local
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    Module.Finite A B ∧ IsLocalHom (algebraMap A B) := by
  haveI := dvr_extension_module_finite A K L B
  exact ⟨inferInstance, dvr_extension_isLocalHom A B⟩









theorem pth_root_unity_eq_one_of_no_prim_root
    (L : Type*) [Field L] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hno : ∀ ω : L, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have h1 : orderOf η ∣ p := orderOf_dvd_of_pow_eq_one hη
  rcases hp.out.eq_one_or_self_of_dvd (orderOf η) h1 with h | h
  · rwa [orderOf_eq_one_iff] at h
  · exact absurd (h ▸ IsPrimitiveRoot.orderOf η) (hno η)

lemma prod_mem_ideal_pow {R : Type*} [CommRing R] (I : Ideal R)
    (s : Finset ℕ) (f : ℕ → R) (hf : ∀ i ∈ s, f i ∈ I) :
    ∏ i ∈ s, f i ∈ I ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top]
  | insert a s hna ih =>
    rw [Finset.prod_insert hna, Finset.card_insert_of_notMem hna, pow_succ']
    exact Ideal.mul_mem_mul (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem no_prim_root_in_unramified_ext_of_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (ω : L) : ¬IsPrimitiveRoot ω p := by
  intro hprim

  have hmap_le : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
      IsLocalRing.maximalIdeal B := by
    have h := Ideal.le_pow_of_le_ramificationIdx
      (show 1 ≤ (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
       from he.symm ▸ le_refl 1)
    simpa [pow_one] using h

  have hp_mem_B : (↑p : B) ∈ IsLocalRing.maximalIdeal B := by
    have hp_mem_A : (↑p : A) ∈ IsLocalRing.maximalIdeal A :=
      habsunram ▸ Ideal.subset_span (Set.mem_singleton _)
    have := hmap_le (Ideal.mem_map_of_mem _ hp_mem_A)
    rwa [map_natCast] at this

  have hp_not_sq : (↑p : B) ∉ (IsLocalRing.maximalIdeal B) ^ 2 := by
    intro h
    have hnotmap : ¬(Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
        (IsLocalRing.maximalIdeal B) ^ 2) := by
      rw [← Ideal.ramificationIdx_ne_one_iff hmap_le]; omega
    apply hnotmap
    rw [← habsunram, Ideal.map_span, Ideal.span_le]
    rintro x ⟨a, rfl, rfl⟩
    rwa [map_natCast]

  haveI hcharB : CharP (IsLocalRing.ResidueField B) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    rw [show (↑p : IsLocalRing.ResidueField B) = (IsLocalRing.residue B) (↑p : B) from
      (map_natCast (IsLocalRing.residue B) p).symm]
    exact (IsLocalRing.residue_eq_zero_iff (↑p : B)).mpr hp_mem_B

  have hp_ne_zero_A : (↑p : A) ≠ 0 := by
    intro h
    have : IsLocalRing.maximalIdeal A = ⊥ := by rw [← habsunram, h]; simp
    exact IsDiscreteValuationRing.not_isField A
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)

  have hp_ne_zero_K : (↑p : K) ≠ 0 := by
    intro h
    apply hp_ne_zero_A
    have : algebraMap A K (↑p : A) = 0 := by rwa [map_natCast]
    exact (IsFractionRing.injective A K) (this.trans (map_zero _).symm)

  by_cases hp2 : p = 2
  · apply hnoroot (-1 : K)
    subst hp2
    have hne : (-1 : K) ≠ 1 := by
      intro h
      apply hp_ne_zero_K
      have h1 : (1 : K) + 1 = 0 := by
        have := neg_add_cancel (1 : K); rwa [h] at this
      have : (2 : K) = 0 := by
        have : (2 : K) = 1 + 1 := by norm_num
        rw [this]; exact h1
      exact_mod_cast this
    constructor
    · norm_num
    · intro l hl
      rw [neg_one_pow_eq_one_iff_even hne] at hl
      exact hl.two_dvd
  ·
    have hp_ge_3 : 3 ≤ p := by have := hp.out.two_le; omega

    obtain ⟨b, hb_eq, hb_prim⟩ : ∃ b : B, algebraMap B L b = ω ∧ IsPrimitiveRoot b p := by
      have hint : IsIntegral B ω := (hprim.isIntegral hp.out.pos).tower_top
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      exact ⟨b, hb, (hb ▸ hprim).of_map_of_injective (IsFractionRing.injective B L)⟩

    have hres_one : IsLocalRing.residue B b = 1 := by
      have hbp : b ^ p = 1 := hb_prim.pow_eq_one
      have hres_pow : (IsLocalRing.residue B b) ^ p = 1 := by
        rw [← map_pow, hbp, map_one]
      have h1 : ((IsLocalRing.residue B b) - 1) ^ p = 0 := by
        rw [sub_pow_char _ 1, one_pow, hres_pow, sub_self]
      have h2 : (IsLocalRing.residue B b) - 1 = 0 := by
        rwa [pow_eq_zero_iff (Nat.Prime.ne_zero hp.out)] at h1
      exact sub_eq_zero.mp h2

    have hmem_max : ∀ k ∈ Finset.range (p - 1),
        1 - b ^ (k + 1) ∈ IsLocalRing.maximalIdeal B := by
      intro k _
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_sub, map_one, map_pow, hres_one, one_pow, sub_self]

    have hprod : ∏ k ∈ Finset.range (p - 1), (1 - b ^ (k + 1)) = (↑p : B) := by
      have hp1 : 1 ≤ p := hp.out.one_le
      have hb' : IsPrimitiveRoot b ((p - 1) + 1) :=
        (show p = (p - 1) + 1 by omega) ▸ hb_prim
      rw [IsPrimitiveRoot.prod_one_sub_pow_eq_order hb']
      push_cast [Nat.cast_sub hp1]
      ring

    have hp_in_pow : (↑p : B) ∈ (IsLocalRing.maximalIdeal B) ^ (p - 1) := by
      rw [← hprod]
      convert prod_mem_ideal_pow (IsLocalRing.maximalIdeal B) (Finset.range (p - 1))
        (fun i => 1 - b ^ (i + 1)) hmem_max using 1
      simp [Finset.card_range]

    exact hp_not_sq (Ideal.pow_le_pow_right (by omega : 2 ≤ p - 1) hp_in_pow)

theorem no_prim_pth_root_in_unramified_ext
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have hnoL : ∀ ω : L, ¬IsPrimitiveRoot ω p :=
    no_prim_root_in_unramified_ext_of_base A K p L B habsunram he hnoroot
  exact pth_root_unity_eq_one_of_no_prim_root L p hnoL η hη

theorem unramified_pth_root_in_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (η : L) (hη : η ^ p = 1) :
    ∃ ζ : K, algebraMap K L ζ = η := by

  by_cases hprim : ∃ ω : K, IsPrimitiveRoot ω p
  ·

    obtain ⟨ω, hω⟩ := hprim
    have hωL : IsPrimitiveRoot (algebraMap K L ω) p :=
      hω.map_of_injective (algebraMap K L).injective
    haveI : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩
    obtain ⟨i, _, hi⟩ := hωL.eq_pow_of_pow_eq_one hη
    exact ⟨ω ^ i, by rw [map_pow, hi]⟩
  ·

    rw [not_exists] at hprim
    have h1 := no_prim_pth_root_in_unramified_ext A K p L B habsunram he hprim η hη
    exact ⟨1, by rw [map_one, h1]⟩

theorem dvr_pth_root_ramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (m : ℕ) (hm : 0 < m) (hdvd : p ∣ m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) ≠ 1 := by

  intro he

  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hpp : Nat.Prime p := hp.out
  obtain ⟨ζ_m, hζ_m⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) hm_ne
  obtain ⟨j, hj⟩ := hdvd
  have hj_pos : 0 < j := Nat.pos_of_ne_zero (by intro h; simp [h] at hj; omega)

  have η_prim : IsPrimitiveRoot (ζ_m ^ j) p := by
    rw [hj] at hζ_m
    have hj_ne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj_pos
    have hj_dvd : j ∣ p * j := dvd_mul_left j p
    have h := hζ_m.pow_of_dvd hj_ne hj_dvd
    rwa [Nat.mul_div_cancel _ hj_pos] at h
  set η := ζ_m ^ j with hη_def

  obtain ⟨ζ, hζ⟩ := unramified_pth_root_in_base A K p L B habsunram he η η_prim.pow_eq_one

  have hζ_pow : ζ ^ p = 1 := by
    have h1 : algebraMap K L (ζ ^ p) = η ^ p := by rw [map_pow, hζ]
    rw [η_prim.pow_eq_one] at h1
    exact (algebraMap K L).injective (h1.trans (map_one _).symm)
  have hζ_eq : ζ = 1 := hno_prim ζ hζ_pow

  have hη_eq : η = 1 := by rw [← hζ, hζ_eq, map_one]
  exact η_prim.ne_one hpp.one_lt hη_eq


theorem cyclotomic_ramified_of_dvd
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (m : ℕ) (hm : 0 < m) (hdvd : p ∣ m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) ≠ 1 :=
  dvr_pth_root_ramified A K p hno_prim m hm hdvd L B habsunram



end
