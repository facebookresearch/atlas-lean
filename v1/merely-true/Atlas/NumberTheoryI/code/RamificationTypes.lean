/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.EisensteinRamified
import Atlas.NumberTheoryI.code.Thm1023
import Atlas.NumberTheoryI.code.Cor1015
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

open Ideal IsLocalRing

section RamificationDefinitions

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

noncomputable abbrev AKLB_residueChar :=
  ringChar (IsLocalRing.ResidueField A)

def AKLB_IsTamelyRamified : Prop :=
  ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B)

def AKLB_IsTotallyTamelyRamified : Prop :=
  AKLB_ramIdx A B = Module.finrank K L ∧ ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B) ∧
  1 < Module.finrank K L

end RamificationDefinitions

section RamificationTransitivity

variable {p e_EK e_EL e_LK : ℕ}

theorem tamelyRamified_of_tower_left
    (hmul : e_EK = e_EL * e_LK) (h : ¬ (p ∣ e_EK)) : ¬ (p ∣ e_LK) :=
  fun hd => h (hmul ▸ dvd_mul_of_dvd_right hd e_EL)

theorem tamelyRamified_of_tower_right
    (hmul : e_EK = e_EL * e_LK) (h : ¬ (p ∣ e_EK)) : ¬ (p ∣ e_EL) :=
  fun hd => h (hmul ▸ dvd_mul_of_dvd_left hd e_LK)

theorem tamelyRamified_tower
    (hp : Nat.Prime p ∨ p = 0)
    (hmul : e_EK = e_EL * e_LK)
    (hEL : ¬ (p ∣ e_EL)) (hLK : ¬ (p ∣ e_LK)) : ¬ (p ∣ e_EK) := by
  rw [hmul]
  rcases hp with hp | rfl
  · exact hp.not_dvd_mul hEL hLK
  · simp only [zero_dvd_iff, mul_eq_zero, not_or] at *
    exact ⟨hEL, hLK⟩

theorem tamelyRamified_tower_iff
    (hp : Nat.Prime p ∨ p = 0)
    (hmul : e_EK = e_EL * e_LK) :
    ¬ (p ∣ e_EK) ↔ ¬ (p ∣ e_EL) ∧ ¬ (p ∣ e_LK) :=
  ⟨fun h => ⟨tamelyRamified_of_tower_right hmul h, tamelyRamified_of_tower_left hmul h⟩,
   fun ⟨hEL, hLK⟩ => tamelyRamified_tower hp hmul hEL hLK⟩

lemma residueChar_prime_or_zero (F : Type*) [Field F] :
    Nat.Prime (ringChar F) ∨ ringChar F = 0 := by
  haveI := ringChar.charP F
  exact CharP.char_is_prime_or_zero F (ringChar F)

variable {f_EK f_EL f_LK : ℕ}

theorem totallyRamified_tower
    (hmul_f : f_EK = f_EL * f_LK)
    (hEL : f_EL = 1) (hLK : f_LK = 1) : f_EK = 1 := by
  rw [hmul_f, hEL, hLK, mul_one]

end RamificationTransitivity

section TotallyTamelyRamifiedCharacterization

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

structure IsNthRootOfUniformizer (n : ℕ) (π : B) (πA : A) : Prop where
  uniformizer_A : Irreducible πA
  pow_eq : π ^ n = algebraMap A B πA
  adjoin_eq_top : Algebra.adjoin A ({π} : Set B) = ⊤

theorem nth_root_of_uniformizer_generates
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (n : ℕ) (hn : 1 < n) (π : B) (πA : A)
    (hπA : Irreducible πA) (hpow : π ^ n = algebraMap A B πA)
    (hn_eq : n = Module.finrank K L) :
    Irreducible π ∧ Algebra.adjoin A ({π} : Set B) = ⊤ := by


  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible (R := B)

  have hπ_ne_zero : π ≠ 0 := by
    intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hpow
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (hpow.symm.trans (map_zero _).symm))
  have hπ_not_unit : ¬IsUnit π := by
    intro h; have := h.pow n; rw [hpow] at this
    exact hπA.1 ((isUnit_map_iff (algebraMap A B) _).mp this)

  have hπ_span_ne_bot : Ideal.span {π} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  obtain ⟨k, hk_eq⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hπ_span_ne_bot hπB

  have h_maxB : IsLocalRing.maximalIdeal B = Ideal.span {πB} := hπB.maximalIdeal_eq

  have hk_max : Ideal.span {π} = (IsLocalRing.maximalIdeal B) ^ k := by
    rw [hk_eq, ← Ideal.span_singleton_pow, h_maxB]

  have hk_pos : 0 < k := by
    by_contra h; push Not at h; interval_cases k
    rw [pow_zero, Ideal.one_eq_top] at hk_max
    exact hπ_not_unit (Ideal.span_singleton_eq_top.mp hk_max)


  have hπA_span : IsLocalRing.maximalIdeal A = Ideal.span {πA} := hπA.maximalIdeal_eq

  have h_map : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      Ideal.span {algebraMap A B πA} := by
    rw [hπA_span, Ideal.map_span, Set.image_singleton]

  have h_span_pow : Ideal.span {algebraMap A B πA} = (Ideal.span {π}) ^ n := by
    rw [Ideal.span_singleton_pow, ← hpow]

  have h_map_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ (n * k) := by
    rw [h_map, h_span_pow, hk_max, ← pow_mul, mul_comm]

  have h_degree := AKLB_degree_eq_ramIdx_mul_resDeg A K B L

  have hπA_B_ne_zero : algebraMap A B πA ≠ 0 := by
    intro h
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (h.trans (map_zero _).symm))

  have hnk_ne : n * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h_map_ne_bot : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [h_map_eq]; exact (pow_ne_zero_iff hnk_ne).mpr
      (IsDiscreteValuationRing.not_a_field B)
  have hPbot : IsLocalRing.maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPprime : (IsLocalRing.maximalIdeal B).IsPrime := Ideal.IsMaximal.isPrime
    (IsLocalRing.maximalIdeal.isMaximal (R := B))
  have he_eq_nk : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      n * k := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count h_map_ne_bot
        hPprime hPbot, h_map_eq, UniqueFactorizationMonoid.normalizedFactors_pow,
        Multiset.count_nsmul,
        UniqueFactorizationMonoid.normalizedFactors_irreducible
          (Ideal.prime_of_isPrime hPbot hPprime).irreducible]
    simp [normalize_eq]


  have he_pos : 0 < (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) := by
    rw [he_eq_nk]; exact Nat.mul_pos (by omega) hk_pos
  have h_fk_eq_1 : AKLB_resDeg A B * k = 1 := by
    have h_n_eq_ef : n = (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
        * AKLB_resDeg A B := by rw [hn_eq]; exact h_degree
    nlinarith [he_eq_nk]
  have hk_eq_1 : k = 1 := Nat.eq_one_of_mul_eq_one_left h_fk_eq_1
  have hf_eq_1 : AKLB_resDeg A B = 1 := Nat.eq_one_of_mul_eq_one_right h_fk_eq_1

  have h_span_eq : Ideal.span {π} = IsLocalRing.maximalIdeal B := by
    rw [hk_max, hk_eq_1, pow_one]
  have hπ_irr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr h_span_eq.symm

  have htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L := by
    rw [he_eq_nk, hk_eq_1, mul_one, hn_eq]
  constructor
  · exact hπ_irr
  · exact totally_ramified_adjoin_uniformizer A K B L π hπ_irr htotram

theorem uniformizer_pow_associated_algebraMap
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA₀ : A) (hπA₀ : Irreducible πA₀)
    (πB : B) (hπB : Irreducible πB) :
    ∃ u : Bˣ, πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀ := by

  have hne : algebraMap A B πA₀ ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A B)]
    exact hπA₀.ne_zero

  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπB

  have hram : (maximalIdeal A).ramificationIdx (maximalIdeal B) = m := by

    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = (maximalIdeal B) ^ m := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πA₀).mp hπA₀,
          Ideal.map_span, Set.image_singleton, hv]
      rw [show (↑v : B) * πB ^ m = πB ^ m * ↑v from mul_comm _ _,
          ← Ideal.span_singleton_mul_span_singleton]
      simp [Ideal.span_singleton_eq_top.mpr (Units.isUnit v),
            ← Ideal.span_singleton_pow,
            ← (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB]
    have hmap_ne : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ := by
      rw [hmap, (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
          Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
      exact pow_ne_zero _ hπB.ne_zero
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hmap_ne
          (Ideal.IsMaximal.isPrime' (maximalIdeal B)),
        hmap]
    apply multiplicity_pow_self
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
          ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hπB.ne_zero
    · rw [Ideal.isUnit_iff]
      exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top

  have hm : m = Module.finrank K L := by
    rw [← htotram]; exact hram.symm

  refine ⟨v⁻¹, ?_⟩
  rw [hm] at hv
  rw [hv, ← mul_assoc]
  simp

theorem hensel_unit_nth_root_of_one_mod
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (n : ℕ) (hn : 1 < n)
    (hp : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n))
    (u : Bˣ) (hu_mod : (u : B) - 1 ∈ IsLocalRing.maximalIdeal B) :
    ∃ r : Bˣ, (↑r : B) ^ n = ↑u := by
  open Polynomial IsLocalRing in
  haveI : HenselianRing B (maximalIdeal B) := inferInstance
  set f := X ^ n - C (u : B)
  have hf_monic : f.Monic := monic_X_pow_sub_C _ (by omega)

  have hf_eval : f.eval 1 ∈ maximalIdeal B := by
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [show (1 : B) - ↑u = -(↑u - 1) from by ring]
    exact (maximalIdeal B).neg_mem hu_mod

  have hf_deriv : IsUnit (Ideal.Quotient.mk (maximalIdeal B) (f.derivative.eval 1)) := by
    simp only [f, derivative_sub, derivative_C, sub_zero, derivative_pow, derivative_X, mul_one,
      eval_mul, eval_pow, eval_X, one_pow, mul_one, map_natCast, eval_natCast]
    change IsUnit ((n : ResidueField B))
    rw [isUnit_iff_ne_zero]; exact fun h => hp (ringChar.dvd h)

  obtain ⟨a, ha_root, ha_close⟩ := HenselianRing.is_henselian f hf_monic 1 hf_eval hf_deriv

  have ha_pow : a ^ n = (u : B) := by
    have h : f.eval a = 0 := ha_root
    simp only [f, eval_sub, eval_pow, eval_X, eval_C] at h
    exact sub_eq_zero.mp h

  have ha_unit : IsUnit a := by
    by_contra ha_nmem
    have ha_mem : a ∈ maximalIdeal B := ha_nmem
    have h1_mem : (1 : B) ∈ maximalIdeal B := by
      have : (1 : B) = a - (a - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ ha_mem ha_close
    have := (maximalIdeal.isMaximal B).ne_top
    rw [Ideal.ne_top_iff_one] at this; exact this h1_mem
  obtain ⟨r, rfl⟩ := ha_unit
  exact ⟨r, ha_pow⟩

theorem uniformizer_adjust_mod_maximal
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA₀ : A) (hπA₀ : Irreducible πA₀)
    (πB : B) (hπB : Irreducible πB)
    (u : Bˣ) (hu : πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀) :
    ∃ (πA₁ : A) (u₁ : Bˣ),
      Irreducible πA₁ ∧
      πB ^ (Module.finrank K L) = ↑u₁ * algebraMap A B πA₁ ∧
      ((u₁ : B) - 1) ∈ IsLocalRing.maximalIdeal B := by

  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L

  have hn_pos : 0 < Module.finrank K L := Module.finrank_pos
  have hf1 : AKLB_resDeg A B = 1 := by
    rw [htotram] at hfund; nlinarith

  have hsurj : Function.Surjective
      (algebraMap (ResidueField A) (ResidueField B)) := by
    haveI : FiniteDimensional (ResidueField A) (ResidueField B) :=
      FiniteDimensional.of_finrank_pos (by change 0 < AKLB_resDeg A B; omega)
    have hrange : (Algebra.linearMap (ResidueField A) (ResidueField B)).range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj
            (algebraMap (ResidueField A) (ResidueField B)).injective,
          Module.finrank_self]; exact hf1.symm

    rwa [LinearMap.range_eq_top] at hrange

  obtain ⟨abar, habar⟩ := hsurj ((residue B) (u : B))
  obtain ⟨a, ha⟩ := residue_surjective (R := A) abar

  have hres_eq : (residue B) ((algebraMap A B) a) = (residue B) (u : B) := by
    have h1 := RingHom.congr_fun (ResidueField.map_comp_residue (algebraMap A B)) a
    simp only [RingHom.comp_apply] at h1
    rw [← h1, ha]; exact habar

  have ha_unit : IsUnit a := by
    by_contra h_nonunit
    have ha_mem : a ∈ maximalIdeal A := by rwa [mem_maximalIdeal]
    have hab_mem : (algebraMap A B) a ∈ maximalIdeal B :=
      map_nonunit (algebraMap A B) a ha_mem
    rw [← residue_eq_zero_iff] at hab_mem
    rw [hres_eq] at hab_mem
    exact (RingHom.isUnit_map _ u.isUnit).ne_zero hab_mem
  obtain ⟨aA, haA⟩ := ha_unit

  set bA := Units.map (algebraMap A B).toMonoidHom aA with hbA_def
  refine ⟨(aA : A) * πA₀, u * bA⁻¹, ?_, ?_, ?_⟩
  ·
    exact (associated_unit_mul_right πA₀ aA aA.isUnit).irreducible hπA₀
  ·
    rw [Units.val_mul, map_mul]
    have hbA_inv_val : (↑bA⁻¹ : B) = algebraMap A B (↑aA⁻¹ : A) := by simp [bA]
    have h_cancel : (algebraMap A B) (↑aA⁻¹ : A) * (algebraMap A B) (↑aA : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [show ↑u * ↑bA⁻¹ * ((algebraMap A B) ↑aA * (algebraMap A B) πA₀) =
      ↑u * (↑bA⁻¹ * (algebraMap A B) ↑aA) * (algebraMap A B) πA₀ from by ring]
    rw [hbA_inv_val, h_cancel, mul_one]
    exact hu
  ·
    rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    show (residue B) (↑(u * bA⁻¹)) = 1
    rw [Units.val_mul, map_mul]

    have hbA_val : (↑bA : B) = algebraMap A B (↑aA : A) := by simp [bA]
    rw [← haA] at hres_eq
    rw [← hbA_val] at hres_eq

    rw [← hres_eq, ← map_mul, Units.mul_inv, map_one]

lemma isPrecomplete_of_pow
    {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    (e : ℕ) (he : 1 ≤ e) [hpc : IsPrecomplete (I ^ e) M] :
    IsPrecomplete I M := by
  constructor
  intro f hf
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f (m * e) ≡ f (n * e) [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
    intro m n hmn
    rw [show (I ^ e) ^ m = I ^ (m * e) from by rw [← pow_mul, mul_comm]]
    exact hf (Nat.mul_le_mul_right e hmn)
  obtain ⟨L, hL⟩ := hpc.prec' (fun n => f (n * e)) hcauchy
  exact ⟨L, fun n => by
    have h1 : f n ≡ f (n * e) [SMOD I ^ n • (⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_right n (by omega))
    have h2 : f (n * e) ≡ L [SMOD (I ^ e) ^ n • (⊤ : Submodule R M)] := hL n
    rw [show (I ^ e) ^ n = I ^ (n * e) from by rw [← pow_mul, mul_comm]] at h2
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n (by omega)))) h2)⟩

set_option maxHeartbeats 400000 in
theorem finite_extension_adic_complete
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B] :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  rw [isAdicComplete_iff]
  refine ⟨inferInstance, ?_⟩

  have hpc_A : IsPrecomplete (IsLocalRing.maximalIdeal A) B := by
    rw [← AdicCompletion.of_surjective_iff]
    set I := IsLocalRing.maximalIdeal A
    have hsurj_tp := AdicCompletion.ofTensorProduct_surjective_of_finite I B
    have hsurj_A : Function.Surjective (AdicCompletion.of I A) :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).2
    suffices h : ∀ t, AdicCompletion.ofTensorProduct I B t ∈
        LinearMap.range (AdicCompletion.of I B) by
      intro y
      obtain ⟨t, ht⟩ := hsurj_tp y
      exact ⟨(h t).choose, by rw [(h t).choose_spec, ht]⟩
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r b =>
      obtain ⟨a, ha⟩ := hsurj_A r
      exact ⟨a • b, by
        rw [AdicCompletion.ofTensorProduct_tmul, ← ha, map_smul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨bx, hbx⟩ := hx
      obtain ⟨by_, hby⟩ := hy
      exact ⟨bx + by_, by simp [map_add, hbx, hby]⟩

  have hpc_map : IsPrecomplete (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr hpc_A

  set J := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hJ_def
  have hle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [hJ_def, Ideal.map_eq_bot_iff_le_ker] at h
    have hker : RingHom.ker (algebraMap A B) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
    rw [hker] at h
    exact IsDiscreteValuationRing.not_a_field A (le_bot_iff.mp h)
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) J hJne
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e
    simp only [pow_zero, Ideal.one_eq_top] at he
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (he ▸ hle))

  rw [he] at hpc_map
  exact isPrecomplete_of_pow e he1 (hpc := hpc_map)

theorem residue_char_eq_of_local_hom
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) := by


  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
  exact (Algebra.ringChar_eq (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).symm

theorem totally_tamely_ramified_has_nth_root
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (htame : ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B))
    (hn1 : 1 < Module.finrank K L) :
    ∃ (πA : A) (π : B),
      Irreducible πA ∧ π ^ (Module.finrank K L) = algebraMap A B πA ∧
      Algebra.adjoin A ({π} : Set B) = ⊤ := by
  set n := Module.finrank K L with hn_def


  have key : ∃ (πA₀ : A) (πB : B) (u : Bˣ) (r : Bˣ),
      Irreducible πA₀ ∧ 1 < n ∧ πB ^ n = ↑u * algebraMap A B πA₀ ∧ (↑r : B) ^ n = ↑u := by

    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B


    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB

    obtain ⟨πA₁, u₁, hπA₁, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB u₀ hu₀


    haveI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B

    have hchar : ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) :=
      residue_char_eq_of_local_hom A B

    have htame_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n) := by
      rw [hchar]; rwa [htotram] at htame
    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B n hn1 htame_B u₁ hu₁_mod
    exact ⟨πA₁, πB, u₁, r, hπA₁, hn1, hu₁, hr⟩

  obtain ⟨πA₀, πB, u, r, hπA₀, hn1, hu, hr⟩ := key


  refine ⟨πA₀, πB * ↑(r⁻¹ : Bˣ), hπA₀, ?_, ?_⟩
  ·
    have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
      rw [inv_pow]; congr 1; ext; exact hr
    rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
    rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
    simp [Units.mul_inv]
  ·
    have hpow : (πB * ↑(r⁻¹ : Bˣ)) ^ n = algebraMap A B πA₀ := by
      have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
        rw [inv_pow]; congr 1; ext; exact hr
      rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
      rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
      simp [Units.mul_inv]
    have := nth_root_of_uniformizer_generates A K B L n hn1
      (πB * ↑(r⁻¹ : Bˣ)) πA₀ hπA₀ hpow rfl
    exact this.2

theorem totallyTamelyRamified_of_nthRootOfUniformizer
    (hn : 1 < Module.finrank K L)
    (π : B) (πA : A) (hroot : IsNthRootOfUniformizer A B (Module.finrank K L) π πA)
    (htame : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
    AKLB_IsTotallyTamelyRamified A K B L := by

  have ⟨hπ_irr, hadj⟩ :=
    nth_root_of_uniformizer_generates A K B L (Module.finrank K L) hn π πA
      hroot.uniformizer_A hroot.pow_eq rfl


  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_surj_of_adjoin_uniformizer π hπ_irr hadj
  have hf1 : AKLB_resDeg A B = 1 :=
    finrank_eq_one_of_algebraMap_surjective hsurj
  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [hf1, mul_one] at hfund


  exact ⟨hfund.symm, hfund.symm ▸ htame, hn⟩

theorem nthRootOfUniformizer_of_totallyTamelyRamified
    (httr : AKLB_IsTotallyTamelyRamified A K B L) :
    ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
  obtain ⟨htotram, htame, hlt⟩ := httr
  obtain ⟨πA, π, hπA, hpow, hadj⟩ :=
    totally_tamely_ramified_has_nth_root A K B L htotram htame hlt
  exact ⟨πA, π, hπA, hpow, hadj⟩

theorem totallyTamelyRamified_iff_nthRootOfUniformizer
    (hn : 1 < Module.finrank K L)
    (htame_deg : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
    AKLB_IsTotallyTamelyRamified A K B L ↔
    ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
  constructor
  · exact nthRootOfUniformizer_of_totallyTamelyRamified A K B L
  · rintro ⟨πA, π, hroot⟩
    exact totallyTamelyRamified_of_nthRootOfUniformizer A K B L hn π πA hroot htame_deg

end TotallyTamelyRamifiedCharacterization

section PadicDecompositionArithmetic

theorem padic_decomp_exists (e : ℕ) (he : e ≠ 0) (p : ℕ) (hp : Nat.Prime p ∨ p = 0) :
    ∃ m a, e = m * p ^ a ∧ ¬(p ∣ m) := by
  rcases hp with hp | rfl
  · obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd he p hp.one_lt.ne'
    exact ⟨m, a, by rw [heq, mul_comm], hm⟩
  · exact ⟨e, 0, by simp, by simp [he]⟩

theorem padic_decomp_unique (p : ℕ) (hp : Nat.Prime p ∨ p = 0) (m₁ m₂ a₁ a₂ : ℕ)
    (hm₁ : ¬(p ∣ m₁)) (hm₂ : ¬(p ∣ m₂))
    (hne : m₁ * p ^ a₁ ≠ 0)
    (heq : m₁ * p ^ a₁ = m₂ * p ^ a₂) : m₁ = m₂ ∧ a₁ = a₂ := by
  rcases hp with hp | rfl
  ·
    suffices ha : a₁ = a₂ by
      subst ha
      exact ⟨Nat.eq_of_mul_eq_mul_right
        (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq, rfl⟩
    by_contra hab

    have key : ∀ {m₁ m₂ a₁ a₂ : ℕ}, ¬(p ∣ m₁) →
        m₁ * p ^ a₁ = m₂ * p ^ a₂ → a₁ < a₂ → False := by
      intro m₁ m₂ a₁ a₂ hm heq h
      have heq' : m₁ * p ^ a₁ = m₂ * p ^ (a₂ - a₁) * p ^ a₁ := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt h)]; exact heq
      have hm₁eq : m₁ = m₂ * p ^ (a₂ - a₁) :=
        Nat.eq_of_mul_eq_mul_right
          (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq'
      exact hm (hm₁eq ▸ dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m₂)
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key hm₁ heq h
    · exact key hm₂ heq.symm h
  ·
    simp only [zero_dvd_iff] at hm₁ hm₂
    rcases Nat.eq_zero_or_pos a₁ with rfl | ha₁ <;>
      rcases Nat.eq_zero_or_pos a₂ with rfl | ha₂
    · simp at heq; exact ⟨heq, rfl⟩
    · simp [zero_pow (by omega : a₂ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at hne

theorem padic_decomp_unique_tower (p : ℕ) (hp : Nat.Prime p ∨ p = 0)
    {e m₁ m₂ a₁ a₂ : ℕ} (he : e ≠ 0)
    (heq₁ : e = m₁ * p ^ a₁) (hm₁ : ¬(p ∣ m₁))
    (heq₂ : e = m₂ * p ^ a₂) (hm₂ : ¬(p ∣ m₂)) :
    m₁ = m₂ ∧ a₁ = a₂ :=
  padic_decomp_unique p hp m₁ m₂ a₁ a₂ hm₁ hm₂ (heq₁ ▸ he) (by rw [← heq₂, ← heq₁])

end PadicDecompositionArithmetic

section TameWildDecompositionTotallyRamified

lemma IntermediateField.adjoin_singleton_eq_of_smul
    {K L : Type*} [Field K] [Field L] [Algebra K L] (α β : L)
    (h1 : ∃ k : K, algebraMap K L k * β = α)
    (h2 : ∃ k : K, algebraMap K L k * α = β) :
    IntermediateField.adjoin K ({α} : Set L) = IntermediateField.adjoin K ({β} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h1; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {β} rfl)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h2; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {α} rfl)

lemma ratio_pow_eq_one {L : Type*} [Field L] (α β c : L) (m : ℕ)
    (hα : α ^ m = c) (hβ : β ^ m = c) (hc : c ≠ 0) :
    (α * β⁻¹) ^ m = 1 := by
  rw [mul_pow, hα, inv_pow, hβ, mul_inv_cancel₀ hc]





theorem hensel_dvr_mth_root_of_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (hm_dvd : m ∣ Module.finrank K L) :
    ∃ (ϖ : A) (π : L), Irreducible ϖ ∧ π ^ m = algebraMap K L (algebraMap A K ϖ) ∧ π ≠ 0 := by

  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact hm (dvd_zero _)

  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    refine ⟨ϖ, algebraMap K L (algebraMap A K ϖ), hϖ, pow_one _, ?_⟩
    simp only [ne_eq, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A K)]
    exact hϖ.ne_zero

  · have hm_ge2 : 1 < m := by omega

    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB_irr⟩ := IsDiscreteValuationRing.exists_irreducible B

    haveI hB_complete : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B

    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB_irr

    obtain ⟨ϖ, u₁, hϖ, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB_irr u₀ hu₀

    have hm_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ m) := by
      rwa [residue_char_eq_of_local_hom A B]

    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B m hm_ge2 hm_B u₁ hu₁_mod


    set n := Module.finrank K L with hn_def
    obtain ⟨k, hk⟩ := hm_dvd

    set πB_L := algebraMap B L πB
    set r_L := algebraMap B L (↑r : B)
    have hr_L_ne : r_L ≠ 0 := by
      simp only [r_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
      exact Units.ne_zero r
    refine ⟨ϖ, πB_L ^ k / r_L, hϖ, ?_, ?_⟩
    ·
      rw [div_pow, ← pow_mul, mul_comm k m, ← hk]


      have h1 : πB_L ^ n = algebraMap B L (↑u₁ : B) * algebraMap B L (algebraMap A B ϖ) := by
        rw [← map_pow, hu₁, map_mul]


      have h2 : r_L ^ m = algebraMap B L (↑u₁ : B) := by
        rw [← map_pow, hr]


      have h3 : algebraMap B L (algebraMap A B ϖ) = algebraMap K L (algebraMap A K ϖ) := by
        rw [← IsScalarTower.algebraMap_apply A B L,
            ← IsScalarTower.algebraMap_apply A K L]

      rw [h2, h1, h3]
      have hu_L_ne : algebraMap B L (↑u₁ : B) ≠ 0 := by
        simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact Units.ne_zero u₁
      field_simp
    ·
      apply div_ne_zero
      · apply pow_ne_zero
        show πB_L ≠ 0
        simp only [πB_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact hπB_irr.ne_zero
      · exact hr_L_ne

theorem hensel_uniformizer_construction
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m a : ℕ) (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (πA_img : K) (π : L),
      π ^ m = algebraMap K L πA_img ∧
      algebraMap K L πA_img ≠ 0 ∧
      π ≠ 0 ∧
      Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧
      Module.finrank (IntermediateField.adjoin K ({π} : Set L)) L =
        (AKLB_residueChar A) ^ a ∧
      (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by


  have core : ∃ (πA_img : K) (π : L),
      π ^ m = algebraMap K L πA_img ∧
      algebraMap K L πA_img ≠ 0 ∧
      π ≠ 0 ∧
      Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧
      (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by


    obtain ⟨ϖ, π, hϖ_irr, hπ_pow, hπ_ne⟩ :=
      hensel_dvr_mth_root_of_uniformizer A K B L htotram m hm
        ⟨(AKLB_residueChar A) ^ a, hma⟩

    have hπA_img_ne : algebraMap K L (algebraMap A K ϖ) ≠ 0 := by
      simp only [ne_eq, map_eq_zero]
      rw [← map_zero (algebraMap A K)]
      exact (IsFractionRing.injective A K).ne hϖ_irr.ne_zero


    have step_iii : Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m := by

      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp only [zero_mul] at hma
          linarith [Module.finrank_pos (R := K) (M := L)]
        · exact h
      have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos

      open Polynomial in
      have heis : (X ^ m - C ϖ : Polynomial A).IsEisensteinAt
          (IsLocalRing.maximalIdeal A) := by
        apply (monic_X_pow_sub_C ϖ hm_ne).isEisensteinAt_of_mem_of_notMem
        · exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        · intro n hn
          rw [natDegree_X_pow_sub_C] at hn
          simp only [coeff_sub, coeff_X_pow, coeff_C,
            if_neg (Nat.ne_of_lt hn), zero_sub, neg_mem_iff]
          split_ifs with h0
          · subst h0; rw [IsLocalRing.mem_maximalIdeal]; exact hϖ_irr.1
          · exact (IsLocalRing.maximalIdeal A).zero_mem
        · simp only [coeff_sub, coeff_X_pow, coeff_C, eq_comm, hm_ne, if_false,
            if_true, zero_sub]
          rw [Ideal.neg_mem_iff, hϖ_irr.maximalIdeal_eq, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          intro ⟨a, ha⟩; rw [sq, mul_assoc] at ha
          exact hϖ_irr.1 (IsUnit.of_mul_eq_one a
            (mul_left_cancel₀ hϖ_irr.ne_zero (by rw [mul_one]; exact ha)).symm)

      open Polynomial in
      have hirr_A : Irreducible (X ^ m - C ϖ : Polynomial A) :=
        heis.irreducible inferInstance (monic_X_pow_sub_C ϖ hm_ne).isPrimitive
          (by rw [natDegree_X_pow_sub_C]; exact hm_pos)

      open Polynomial in
      have hirr_K : Irreducible (X ^ m - C (algebraMap A K ϖ) : Polynomial K) := by
        have := (monic_X_pow_sub_C ϖ hm_ne).irreducible_iff_irreducible_map_fraction_map
          (K := K) |>.mp hirr_A
        simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] at this
        exact this

      open Polynomial in
      have hroot : aeval π (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = 0 := by
        simp [map_sub, map_pow, aeval_X, aeval_C, hπ_pow]

      open Polynomial in
      have hminpoly : (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = minpoly K π :=
        minpoly.eq_of_irreducible_of_monic hirr_K hroot
          (monic_X_pow_sub_C (algebraMap A K ϖ) hm_ne)

      open Polynomial in
      have hdeg : (minpoly K π).natDegree = m := by
        rw [← hminpoly, natDegree_X_pow_sub_C]

      rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite K π), hdeg]
    exact ⟨algebraMap A K ϖ, π, hπ_pow, hπA_img_ne, hπ_ne, step_iii, ⟨ϖ, hϖ_irr, rfl⟩⟩


  obtain ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, hπA_irr_info⟩ := core
  refine ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, ?_, hπA_irr_info⟩


  set F := IntermediateField.adjoin K ({π} : Set L)
  have htower : Module.finrank K L = Module.finrank K F * Module.finrank F L := by
    rw [← Module.finrank_mul_finrank K (↥F) L]
  rw [hma, hrank_Kπ] at htower


  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [zero_mul] at hma
      linarith [Module.finrank_pos (R := K) (M := L)]
    · exact h
  exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp hm_pos) htower.symm






theorem uniformizerPreimage
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) :
    ∃ πA : A, algebraMap A K πA = πA_img ∧
      πA ∈ IsLocalRing.maximalIdeal A ∧
      πA ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
  obtain ⟨πA, hπA_irr, hπA_eq⟩ := hπA_img
  refine ⟨πA, hπA_eq, ?_, ?_⟩
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton πA)
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h, Ideal.span_singleton_pow]
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hne : πA ≠ 0 := hπA_irr.ne_zero
    have h1 : πA * (πA * c) = πA := by
      calc πA * (πA * c) = πA ^ 2 * c := by ring
      _ = πA := hc.symm
    have h2 : πA * c = 1 :=
      mul_left_cancel₀ hne (h1.trans (mul_one πA).symm)
    exact hπA_irr.not_isUnit ⟨⟨πA, c, h2, by rw [mul_comm]; exact h2⟩, rfl⟩

theorem irreducible_xm_sub_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (hm_pos : 0 < m) :
    Irreducible (Polynomial.X ^ m - Polynomial.C πA_img : Polynomial K) := by

  obtain ⟨πA, hπA_eq, hπA_mem, hπA_sq⟩ :=
    uniformizerPreimage A K B L htotram πA_img hπA hπA_img

  set f : Polynomial A := Polynomial.X ^ m - Polynomial.C πA with hf_def

  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C πA (by omega)

  have hf_deg : f.natDegree = m := Polynomial.natDegree_X_pow_sub_C

  have hf_eis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
    constructor
    ·
      rw [Polynomial.Monic.leadingCoeff hf_monic]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal (R := A)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    ·
      intro n hn
      rw [hf_deg] at hn
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : n ≠ m := by omega
      simp only [if_neg hne]
      by_cases h0 : n = 0
      · simp [h0, hπA_mem]
      · simp [h0]
    ·
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : (0 : ℕ) ≠ m := by omega
      simp only [if_neg hne, zero_sub]
      intro h
      exact hπA_sq (neg_mem_iff.mp h)

  have hirr_A : Irreducible f :=
    hf_eis.irreducible (IsLocalRing.maximalIdeal.isMaximal (R := A)).isPrime
      hf_monic.isPrimitive (by rw [hf_deg]; omega)

  have hirr_K : Irreducible (f.map (algebraMap A K)) :=
    hf_monic.irreducible_iff_irreducible_map_fraction_map.mp hirr_A

  have hmap : f.map (algebraMap A K) = Polynomial.X ^ m - Polynomial.C πA_img := by
    simp [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hπA_eq]
  rwa [hmap] at hirr_K


theorem tameWildDecomposition_existence
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m a : ℕ) (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (T : IntermediateField K L),
      Module.finrank K T = m ∧
      Module.finrank T L = (AKLB_residueChar A) ^ a := by
  obtain ⟨πA_img, π, _, _, _, hT_deg, hT_wild, _⟩ :=
    hensel_uniformizer_construction A K B L htotram m a hma hm

  exact ⟨IntermediateField.adjoin K ({π} : Set L), hT_deg, hT_wild⟩



end TameWildDecompositionTotallyRamified

section TameWildDecompositionGeneral

noncomputable def intClE_to_L_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] L :=
  (E.val.restrictScalars A).comp (integralClosure A ↥E).val

noncomputable def intClE_to_B_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] B := by
  letI : Algebra ↥(integralClosure A ↥E) L :=
    (intClE_to_L_algHom A E).toAlgebra
  haveI : IsScalarTower A ↥(integralClosure A ↥E) L :=
    IsScalarTower.of_algHom (intClE_to_L_algHom A E)
  haveI : Algebra.IsIntegral A ↥(integralClosure A ↥E) :=
    integralClosure.AlgebraIsIntegral
  exact IsIntegralClosure.lift A B L





















end TameWildDecompositionGeneral
