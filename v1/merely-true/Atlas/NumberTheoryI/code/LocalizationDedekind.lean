/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section LocalizationPrimeIdeal

set_option linter.unusedSectionVars false

variable {A : Type*} [CommRing A] [IsDomain A]
variable (S : Submonoid A)
variable {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]


def localization_primeIdeal_orderIso :
    { 𝔮 : Ideal B // 𝔮.IsPrime } ≃o
    { 𝔭 : Ideal A // 𝔭.IsPrime ∧ Disjoint (S : Set A) (𝔭 : Set A) } :=
  IsLocalization.orderIsoOfPrime S B

end LocalizationPrimeIdeal

noncomputable section

set_option linter.unusedSectionVars false

variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def Submodule.localizedInField {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]
    (M : Submodule A K) (S : Submonoid A) : Submodule A K where
  carrier := {x : K | ∃ m ∈ M, ∃ s ∈ S, (s : A) • x = m}
  add_mem' := by
    rintro a b ⟨ma, hma, sa, hsa, ha⟩ ⟨mb, hmb, sb, hsb, hb⟩
    exact ⟨(sb : A) • ma + (sa : A) • mb,
      M.add_mem (M.smul_mem sb hma) (M.smul_mem sa hmb),
      sa * sb, S.mul_mem hsa hsb, by
        simp only [smul_add, mul_smul]; congr 1; rw [smul_comm, ha]; rw [hb]⟩
  zero_mem' := ⟨0, M.zero_mem, 1, S.one_mem, by simp⟩
  smul_mem' := by
    intro c x ⟨m, hm, s, hs, hsx⟩
    exact ⟨(c : A) • m, M.smul_mem c hm, s, hs, by rw [smul_comm, hsx]⟩


theorem submodule_eq_iInf_localizedInField_maximal (M : Submodule A K) :
    (⨅ (v : MaximalSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M := by
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  ·
    intro hx

    let 𝔞 : Ideal A := M.comap (LinearMap.toSpanSingleton A K x)
    by_contra hxM

    have h1 : (1 : A) ∉ 𝔞 := by
      simp only [𝔞, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul]
      exact hxM

    obtain ⟨𝔪, h𝔪max, h𝔞𝔪⟩ := 𝔞.exists_le_maximal (𝔞.ne_top_iff_one.mpr h1)

    obtain ⟨m, hm, s, hs, hsx⟩ := hx ⟨𝔪, h𝔪max⟩

    have hs𝔞 : s ∈ 𝔞 := by
      simp only [𝔞, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      exact hsx ▸ hm

    exact hs (h𝔞𝔪 hs𝔞)
  ·
    intro hx v
    exact ⟨x, hx, 1, v.asIdeal.primeCompl.one_mem', one_smul _ _⟩


theorem submodule_eq_iInf_localizedInField_prime (M : Submodule A K) :
    (⨅ (v : PrimeSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M := by
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  ·
    intro hx
    rw [← submodule_eq_iInf_localizedInField_maximal A K M, Submodule.mem_iInf]
    exact fun v => hx ⟨v.asIdeal, v.isMaximal.isPrime⟩
  · intro hx v
    exact ⟨x, hx, 1, v.asIdeal.primeCompl.one_mem', one_smul _ _⟩


theorem submodule_eq_iInf_localizedInField (M : Submodule A K) :
    (⨅ (v : MaximalSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M ∧
    (⨅ (v : PrimeSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M :=
  ⟨submodule_eq_iInf_localizedInField_maximal A K M, submodule_eq_iInf_localizedInField_prime A K M⟩

theorem subalgebra_iInf_localization_maximal_eq_bot :
    (⨅ v : MaximalSpectrum A,
      Localization.subalgebra.ofField K v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  constructor
  ·

    contrapose
    intro hrange hlocal


    let 𝔞 : Ideal A := (1 : Submodule A K).comap (LinearMap.toSpanSingleton A K x)

    have h1 : (1 : A) ∉ 𝔞 := by simpa [𝔞] using hrange

    rcases 𝔞.exists_le_maximal (𝔞.ne_top_iff_one.mpr h1) with ⟨𝔪, h𝔪, h𝔞𝔪⟩

    rcases hlocal ⟨𝔪, h𝔪⟩ with ⟨n, d, hd, rfl⟩

    exact hd (h𝔞𝔪 ⟨n, by simp [Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ <|
      (map_ne_zero_iff _ <| IsFractionRing.injective A K).mpr
        fun h ↦ hd (h ▸ 𝔪.zero_mem :)]⟩)
  ·

    rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

set_option linter.unusedSectionVars false in

theorem ideal_eq_iInf_comap_map_localization_maximal (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = I := by
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  ·


    intro hx
    by_contra hxI
    have hJ_ne_top : I.colon (Ideal.span {x}) ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one, Ideal.mem_colon_span_singleton]
      simpa using hxI
    obtain ⟨𝔪, h𝔪max, hJ𝔪⟩ := (I.colon (Ideal.span {x})).exists_le_maximal hJ_ne_top
    specialize hx ⟨𝔪, h𝔪max⟩
    rw [Ideal.mem_comap,
      IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    exact hs (hJ𝔪 (Ideal.mem_colon_span_singleton.mpr hsx))
  ·
    intro hxI 𝔪
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI

set_option linter.unusedSectionVars false in

theorem ideal_eq_iInf_comap_map_localization_prime (I : Ideal A) :
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) = I := by
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  ·
    intro hx
    rw [← ideal_eq_iInf_comap_map_localization_maximal A I]
    simp only [Ideal.mem_iInf]
    exact fun 𝔪 => hx ⟨𝔪.asIdeal, 𝔪.isMaximal.isPrime⟩
  · intro hxI 𝔭
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI

set_option linter.unusedSectionVars false in

theorem ideal_eq_iInf_comap_map_localization (I : Ideal A) :
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) =
    (⨅ 𝔭 : PrimeSpectrum A,
      (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) ∧
    (⨅ 𝔪 : MaximalSpectrum A,
      (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap
        (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = I :=
  ⟨by rw [ideal_eq_iInf_comap_map_localization_maximal, ideal_eq_iInf_comap_map_localization_prime], ideal_eq_iInf_comap_map_localization_maximal A I⟩

end

section DedekindDomainCharacterization

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]


theorem isDVR_localization_iff_integrallyClosed_dimensionLEOne :
    (∀ (P : Ideal A), P ≠ ⊥ → ∀ (_ : P.IsPrime),
      IsDiscreteValuationRing (Localization.AtPrime P)) ↔
    (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) := by
  constructor
  ·
    intro h

    have : IsDedekindDomainDvr A := { is_dvr_at_nonzero_prime := h }

    exact ⟨inferInstance, inferInstance⟩
  ·
    intro ⟨hic, hdim⟩

    have : IsDedekindDomain A := { }

    intro P hP hPprime
    exact (IsDedekindDomain.isDedekindDomainDvr A).is_dvr_at_nonzero_prime P hP hPprime

end DedekindDomainCharacterization

section DedekindDomain

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]


theorem integrallyClosed_dimensionLEOne_iff_isDedekindDomain :
    (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) ↔ IsDedekindDomain A := by
  constructor
  · rintro ⟨hic, hdim⟩
    exact { }
  · intro h
    exact ⟨inferInstance, inferInstance⟩

end DedekindDomain

section PrincipalIdealDedekind


theorem pid_isDedekindDomain (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : IsDedekindDomain R :=
  inferInstance


instance Int.isDedekindDomain : IsDedekindDomain ℤ :=
  inferInstance


instance Polynomial.isDedekindDomain (k : Type*) [Field k] :
    IsDedekindDomain (Polynomial k) :=
  inferInstance

end PrincipalIdealDedekind
