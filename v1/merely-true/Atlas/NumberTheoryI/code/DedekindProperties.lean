/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Atlas.NumberTheoryI.code.LocalizationDedekind

class IsSemilocal (A : Type*) [CommRing A] : Prop where
  finite_maximalIdeals : Set.Finite {𝔪 : Ideal A | 𝔪.IsMaximal}

namespace IsSemilocal

variable {A : Type*} [CommRing A]

end IsSemilocal

open Ideal UniqueFactorizationMonoid

theorem Ideal.finite_setOf_isPrime_and_mem {A : Type*} [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (a : A) (ha : a ≠ 0) :
    Set.Finite {P : Ideal A | P.IsPrime ∧ a ∈ P} := by
  have hI : span {a} ≠ ⊥ := by rwa [ne_eq, span_singleton_eq_bot]
  apply Set.Finite.subset ((normalizedFactors (span {a})).toFinset.finite_toSet)
  intro P ⟨hP, haP⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_normalizedFactors_iff hI]
  exact ⟨hP, span_le.mpr (Set.singleton_subset_iff.mpr haP)⟩

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

theorem Ideal.finite_setOf_isPrime_and_le {I : Ideal A} (hI : I ≠ ⊥) :
    {p : Ideal A | p.IsPrime ∧ I ≤ p}.Finite := by
  have hsub : {p : Ideal A | p.IsPrime ∧ I ≤ p} ⊆
    (fun v : HeightOneSpectrum A => v.asIdeal) ''
    {v : HeightOneSpectrum A | v.asIdeal ∣ I} := by
    intro p ⟨hp, hle⟩
    have hpne : p ≠ ⊥ := by
      intro h
      rw [h] at hle
      exact hI (eq_bot_iff.mpr hle)
    exact ⟨⟨p, hp, hpne⟩, Ideal.dvd_iff_le.mpr hle, rfl⟩
  exact (Ideal.finite_factors hI).image (·.asIdeal) |>.subset hsub

theorem Ideal.count_normalizedFactors_eq_zero_iff
    {𝔭 I : Ideal A} (hp : 𝔭.IsPrime) (hI : I ≠ ⊥) :
    Multiset.count 𝔭 (normalizedFactors I) = 0 ↔ ¬(I ≤ 𝔭) := by
  rw [Multiset.count_eq_zero, Ideal.mem_normalizedFactors_iff hI]
  simp [hp]

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem FractionalIdeal.count_eq_zero_for_all_but_finitely_many
    (I : FractionalIdeal A⁰ K) (_ : I ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum A | FractionalIdeal.count K v I ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)

theorem IsDedekindDomain.isPrincipalIdealRing_of_isSemilocal
    (R : Type*) [CommRing R] [IsDedekindDomain R] [IsSemilocal R] :
    IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_finite_maximals IsSemilocal.finite_maximalIdeals

theorem fractionalIdeal_isUnit_iff_isPrincipal
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : FractionalIdeal (nonZeroDivisors A) K) (hI : I ≠ 0) :
    IsUnit I ↔ (I : Submodule A K).IsPrincipal := by
  constructor
  ·

    intro hunit
    have hfin : {J : Ideal A | J.IsMaximal}.Finite := by
      apply Set.Finite.subset (Set.finite_singleton (IsLocalRing.maximalIdeal A))
      intro J hJ
      exact Set.mem_singleton_iff.mpr (IsLocalRing.eq_maximalIdeal hJ)
    obtain ⟨u, hu⟩ := hunit
    have hinv : I * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
    exact FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hfin I ↑u⁻¹ hinv
  ·
    intro hprinc
    haveI : (I : Submodule A K).IsPrincipal := hprinc
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      (FractionalIdeal.invertible_of_principal K I hI)

section FractionalIdealInvertibility

variable {A' : Type*} [CommRing A'] [IsDomain A'] [IsDedekindDomain A']
variable {K' : Type*} [Field K'] [Algebra A' K'] [IsFractionRing A' K']

theorem FractionalIdeal.mul_inv_eq_one_of_ne_zero
    (I : FractionalIdeal A'⁰ K') (hI : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_inv_cancel₀ hI

end FractionalIdealInvertibility

section DedekindQuotientPIR

set_option maxHeartbeats 800000

open Ideal in
lemma isCoprime_span_singleton_of_not_mem_maximal {R : Type*} [CommRing R]
    {P : Ideal R} (hPm : P.IsMaximal) {s : R} (hs : s ∉ P) :
    IsCoprime (Ideal.span {s}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  have h1 : ¬(Ideal.span {s} ⊔ P ≤ P) :=
    fun h => hs (h (mem_sup_left (subset_span rfl)))
  exact hPm.1.2 _ (lt_of_le_of_ne le_sup_right (fun h => h1 (h ▸ le_refl _)))

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

lemma isPrincipalIdealRing_quotient_prime_pow
    (P : Ideal R) [hPm : P.IsMaximal] (n : ℕ) :
    IsPrincipalIdealRing (R ⧸ P ^ n) := by

  have hunit : ∀ (y : P.primeCompl),
      IsUnit ((Ideal.Quotient.mk (P ^ n)) (y : R)) := by
    intro s

    have hcop_n : Ideal.span {(s : R)} ⊔ P ^ n = ⊤ :=
      Ideal.isCoprime_iff_sup_eq.mp
        (isCoprime_span_singleton_of_not_mem_maximal hPm s.2).pow_right
    rw [Ideal.eq_top_iff_one] at hcop_n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hcop_n
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha

    refine .of_mul_eq_one (Ideal.Quotient.mk _ c) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (P ^ n))]
    exact Ideal.Quotient.eq.mpr (show ↑s * c - 1 ∈ P ^ n from by
      rw [show ↑s * c - 1 = -b from by linear_combination hab]
      exact (P ^ n).neg_mem hb)

  let f : Localization.AtPrime P →+* R ⧸ P ^ n :=
    IsLocalization.lift (M := P.primeCompl) hunit
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap R _ r, IsLocalization.lift_eq hunit r⟩
  exact IsPrincipalIdealRing.of_surjective f hsurj

theorem Ideal.Quotient.isPrincipalIdealRing_of_isDedekindDomain
    {I : Ideal R} (hI : I ≠ ⊥) : IsPrincipalIdealRing (R ⧸ I) := by
  classical

  let e := IsDedekindDomain.quotientEquivPiFactors hI
  let ι := (UniqueFactorizationMonoid.factors I).toFinset

  have hPIR : ∀ (P : ι), IsPrincipalIdealRing (R ⧸ (P : Ideal R) ^
      Multiset.count (↑P) (UniqueFactorizationMonoid.factors I)) := by
    intro ⟨P, hP⟩
    have hprime : Prime P :=
      UniqueFactorizationMonoid.prime_of_factor P (Multiset.mem_toFinset.mp hP)
    haveI : P.IsMaximal :=
      Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hprime) hprime.ne_zero
    exact isPrincipalIdealRing_quotient_prime_pow P _

  haveI : ∀ (P : ι), IsPrincipalIdealRing (R ⧸ (P : Ideal R) ^
      Multiset.count (↑P) (UniqueFactorizationMonoid.factors I)) := hPIR
  haveI : IsPrincipalIdealRing (∀ P : ι, R ⧸ (P : Ideal R) ^
      Multiset.count (↑P) (UniqueFactorizationMonoid.factors I)) :=
    Ideal.instIsPrincipalIdealRingForallOfFinite
  exact IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective

end DedekindQuotientPIR

noncomputable section

namespace FractionalIdeal

def localizeAtPrime
    {A : Type*} [CommRing A] [IsDomain A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A) :=
  I.extended (FractionRing A)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective A _))

theorem localizeAtPrime_ne_zero
    {A : Type*} [CommRing A] [IsDomain A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    {I : FractionalIdeal A⁰ (FractionRing A)} (hI : I ≠ 0) :
    I.localizeAtPrime 𝔪 ≠ 0 := by
  intro h; apply hI
  rwa [localizeAtPrime, extended_eq_zero_iff _ _
    (FaithfulSMul.algebraMap_injective A _) zero_notMem_nonZeroDivisors] at h

def IsLocallyPrincipal
    {A : Type*} [CommRing A] [IsDomain A]
    (I : FractionalIdeal A⁰ (FractionRing A)) : Prop :=
  ∀ (𝔪 : Ideal A) [𝔪.IsMaximal],
    ((I.localizeAtPrime 𝔪 :
      Submodule (Localization.AtPrime 𝔪) (FractionRing A)).IsPrincipal)

theorem isUnit_localizeAtPrime_of_isUnit
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A))
    (hI : IsUnit I) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsUnit (I.localizeAtPrime 𝔪) :=
  hI.map (extendedHomₐ (FractionRing A) (Localization.AtPrime 𝔪))

open Classical in
set_option maxHeartbeats 800000 in
theorem inv_localizeAtPrime_le
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (𝔪 : Ideal A) [𝔪.IsPrime]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    (localizeAtPrime 𝔪 I)⁻¹ ≤ localizeAtPrime 𝔪 (I⁻¹) := by
  classical
  unfold localizeAtPrime
  set B := Localization.AtPrime 𝔪
  set K := FractionRing A
  set hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap A B)
    (FaithfulSMul.algebraMap_injective A B)
  have hmap_id : IsLocalization.map K (algebraMap A B) hf = RingHom.id K := by
    apply IsLocalization.ringHom_ext A⁰; ext a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    exact (IsScalarTower.algebraMap_apply A B K a).symm
  have hmap_apply : ∀ y : K, IsLocalization.map K (algebraMap A B) hf y = y := by
    intro y; rw [hmap_id]; rfl
  by_cases hI0 : I = 0
  · subst hI0; simp [extended_zero, inv_zero']
  have hIe0 : I.extended K hf ≠ 0 :=
    extended_ne_zero K hf (FaithfulSMul.algebraMap_injective A B) hI0 zero_notMem_nonZeroDivisors
  obtain ⟨S, hS⟩ := fg_of_isNoetherianRing (le_refl A⁰) I
  have hmem_ext : ∀ g, g ∈ (I : Submodule A K) → g ∈ I.extended K hf := by
    intro g hg
    show g ∈ (↑(I.extended K hf) : Submodule B K)
    rw [coe_extended_eq_span]
    exact Submodule.subset_span ⟨g, hg, hmap_apply g⟩
  intro x hx
  rw [mem_inv_iff hIe0] at hx
  have hxg_int : ∀ g ∈ S, ∃ b : B, algebraMap B K b = x * g := by
    intro g hg
    exact (mem_one_iff B⁰).mp
      (hx _ (hmem_ext g (hS ▸ Submodule.subset_span (Finset.mem_coe.mpr hg))))
  choose bg hbg using hxg_int
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite 𝔪.primeCompl (fun (i : S) => bg i.1 i.2)
  have hkey : ∀ a : A, algebraMap B K (algebraMap A B a) = algebraMap A K a :=
    fun a => (IsScalarTower.algebraMap_apply A B K a).symm
  have hint' : ∀ g (hg : g ∈ S), ∃ a' : A, algebraMap A B a' = algebraMap A B s * bg g hg := by
    intro g hg
    have := hint ⟨g, hg⟩
    simp only [IsLocalization.IsInteger, Algebra.smul_def] at this
    convert this using 1
  have hsx_inv : algebraMap A K s * x ∈ I⁻¹ := by
    rw [mem_inv_iff hI0]
    intro y hy
    rw [mem_one_iff]
    change y ∈ (I : Submodule A K) at hy
    rw [← hS] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro g hg'
      rw [Finset.mem_coe] at hg'
      obtain ⟨a', ha'⟩ := hint' g hg'
      refine ⟨a', ?_⟩
      calc algebraMap A K a'
          = algebraMap B K (algebraMap A B a') := (hkey a').symm
        _ = algebraMap B K (algebraMap A B s * bg g hg') := by rw [ha']
        _ = algebraMap B K (algebraMap A B s) * algebraMap B K (bg g hg') := map_mul _ _ _
        _ = algebraMap A K s * (x * g) := by rw [hkey s, hbg g hg']
        _ = algebraMap A K s * x * g := by ring
    · exact ⟨0, by simp⟩
    · intro y₁ y₂ _ _ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
      exact ⟨a₁ + a₂, by rw [map_add, h₁, h₂, mul_add]⟩
    · intro a y _ ⟨a', ha'⟩
      exact ⟨a * a', by rw [map_mul, ha', Algebra.smul_def, mul_left_comm]⟩
  show x ∈ (↑(extended K hf (I⁻¹)) : Submodule B K)
  rw [coe_extended_eq_span]
  have hsx_in_span : algebraMap A K s * x ∈
      Submodule.span B (IsLocalization.map K (algebraMap A B) hf '' (↑(I⁻¹) : Set K)) :=
    Submodule.subset_span ⟨algebraMap A K s * x, hsx_inv, hmap_apply _⟩
  have hx_eq : x = IsLocalization.mk' B 1 ⟨s, hs⟩ • (algebraMap A K s * x) := by
    rw [Algebra.smul_def, ← mul_assoc]
    have : algebraMap B K (IsLocalization.mk' B 1 ⟨s, hs⟩) * algebraMap A K s = 1 := by
      rw [← hkey s, ← map_mul, IsLocalization.mk'_spec B (1 : A) ⟨s, hs⟩]; simp
    rw [this, one_mul]
  rw [hx_eq]
  exact Submodule.smul_mem _ _ hsx_in_span

theorem isUnit_iff_isUnit_localizeAtPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    IsUnit I ↔ ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], IsUnit (I.localizeAtPrime 𝔪) := by
  constructor
  · exact fun hI 𝔪 _ => isUnit_localizeAtPrime_of_isUnit I hI 𝔪
  · intro h

    rw [← FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)]

    have hle : I * I⁻¹ ≤ 1 := by
      rw [FractionalIdeal.inv_eq]; exact FractionalIdeal.mul_one_div_le_one

    obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle

    suffices hJtop : J = ⊤ by
      rw [← hJ, hJtop, FractionalIdeal.coeIdeal_top]

    by_contra hJne
    obtain ⟨𝔪, h𝔪max, h𝔪le⟩ := J.exists_le_maximal hJne
    haveI : 𝔪.IsMaximal := h𝔪max

    have hunit := h 𝔪
    rw [← FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing A)] at hunit
    have hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (algebraMap A (Localization.AtPrime 𝔪))
      (FaithfulSMul.algebraMap_injective A _)

    have step1 : (1 : FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A)) ≤
        localizeAtPrime 𝔪 I * localizeAtPrime 𝔪 (I⁻¹) :=
      hunit ▸ mul_le_mul' le_rfl (inv_localizeAtPrime_le 𝔪 I)

    have step2 : localizeAtPrime 𝔪 I * localizeAtPrime 𝔪 (I⁻¹) =
        localizeAtPrime 𝔪 (I * I⁻¹) := by
      simp only [localizeAtPrime]
      exact (FractionalIdeal.extended_mul _ hf I I⁻¹).symm

    have step3 : localizeAtPrime 𝔪 (I * I⁻¹) =
        ↑(J.map (algebraMap A (Localization.AtPrime 𝔪))) := by
      have : I * I⁻¹ = ↑J := hJ.symm
      rw [this]
      simp only [localizeAtPrime]
      exact FractionalIdeal.extended_coeIdeal_eq_map _ hf J

    have h1le : (1 : FractionalIdeal (Localization.AtPrime 𝔪)⁰ (FractionRing A)) ≤
        ↑(J.map (algebraMap A (Localization.AtPrime 𝔪))) :=
      step1.trans (step2.le.trans step3.le)

    have hJmap_top : J.map (algebraMap A (Localization.AtPrime 𝔪)) = ⊤ := by
      rw [← FractionalIdeal.coeIdeal_top] at h1le
      exact le_antisymm le_top ((FractionalIdeal.coeIdeal_le_coeIdeal _).mp h1le)

    have h𝔪map_ne_top : 𝔪.map (algebraMap A (Localization.AtPrime 𝔪)) ≠ ⊤ :=
      Ideal.IsPrime.ne_top'

    exact h𝔪map_ne_top (eq_top_iff.mpr (hJmap_top ▸ Ideal.map_mono h𝔪le))

theorem isUnit_iff_isUnit_localizeAtPrime_all_primes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    IsUnit I ↔ ∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsUnit (localizeAtPrime 𝔭 I) := by
  constructor
  · intro hI 𝔭 _
    exact hI.map (extendedHomₐ (FractionRing A) (Localization.AtPrime 𝔭))
  · intro h
    rw [isUnit_iff_isUnit_localizeAtPrime]
    intro 𝔪 h𝔪
    haveI : 𝔪.IsPrime := h𝔪.isPrime
    exact h 𝔪

theorem isUnit_iff_isUnit_localize_prime_maximal
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    (IsUnit I ↔ ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], IsUnit (localizeAtPrime 𝔪 I)) ∧
    (IsUnit I ↔ ∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsUnit (localizeAtPrime 𝔭 I)) :=
  ⟨isUnit_iff_isUnit_localizeAtPrime I, isUnit_iff_isUnit_localizeAtPrime_all_primes I⟩

theorem isUnit_iff_isLocallyPrincipal
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (FractionRing A)) (hI : I ≠ 0) :
    IsUnit I ↔ I.IsLocallyPrincipal := by
  rw [isUnit_iff_isUnit_localizeAtPrime]
  constructor
  · intro h 𝔪 h𝔪
    have hne : I.localizeAtPrime 𝔪 ≠ 0 := localizeAtPrime_ne_zero 𝔪 hI
    exact (fractionalIdeal_isUnit_iff_isPrincipal _ _ _ hne).mp (h 𝔪)
  · intro h 𝔪 h𝔪
    have hne : I.localizeAtPrime 𝔪 ≠ 0 := localizeAtPrime_ne_zero 𝔪 hI
    exact (fractionalIdeal_isUnit_iff_isPrincipal _ _ _ hne).mpr (h 𝔪)

end FractionalIdeal

end
