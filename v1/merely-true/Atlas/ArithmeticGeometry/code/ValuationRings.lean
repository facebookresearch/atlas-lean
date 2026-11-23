/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option maxHeartbeats 800000

open Ideal Submodule

section ValuationRingDef

theorem isValuationSubring_iff_forall_units {K : Type*} [Field K] (R : Subring K) :
    (∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) ↔ (∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) := by
  constructor
  · intro h x _
    exact h x
  · intro h x
    by_cases hx : x = 0
    · left; subst hx; exact R.zero_mem
    · exact h x hx


def ValuationSubring.ofSubring_units {K : Type*} [Field K]
    (R : Subring K) (hR : ∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) :
    ValuationSubring K :=
  ValuationSubring.ofSubring R ((isValuationSubring_iff_forall_units R).mpr hR)

end ValuationRingDef

section Theorem1618

theorem valuationRing_isLocal (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R] :
    IsLocalRing R :=
  inferInstance


end Theorem1618

section Lemma1619

theorem ValuationRing.ideal_le_or_le
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (𝔞 𝔟 : Ideal R) : 𝔞 ≤ 𝔟 ∨ 𝔟 ≤ 𝔞 :=
  (ValuationRing.iff_ideal_total.mp ‹_›).total 𝔞 𝔟

end Lemma1619

theorem ValuationRing.fg_isPrincipal
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (I : Ideal R) (hI : I.FG) : I.IsPrincipal :=
  IsBezout.isPrincipal_of_FG I hI

section Lemma1622

theorem valuationRing_iff_of_localRing (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] :
    (ValuationRing R ∧ ¬IsField R) ↔ (¬IsField R ∧ IsBezout R) := by
  constructor
  ·

    rintro ⟨_, hNF⟩
    exact ⟨hNF, inferInstance⟩
  ·

    rintro ⟨hNF, _⟩
    exact ⟨inferInstance, hNF⟩

end Lemma1622

section LocalRing

theorem localRing_iff_unique_maximal_ideal (R : Type*) [CommSemiring R] :
    IsLocalRing R ↔ ∃! I : Ideal R, I.IsMaximal := by
  constructor
  · intro _
    exact IsLocalRing.maximal_ideal_unique R
  · exact IsLocalRing.of_unique_max_ideal


theorem isLocalRing_iff_nonunits_isIdeal (R : Type*) [CommRing R] :
    IsLocalRing R ↔ ∃ I : Ideal R, (I : Set R) = nonunits R := by
  constructor
  ·
    intro hR
    exact ⟨IsLocalRing.maximalIdeal R, Set.ext fun x =>
      (IsLocalRing.mem_maximalIdeal x).symm⟩
  ·
    rintro ⟨I, hI⟩


    haveI : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h0 : (0 : R) ∈ nonunits R := hI ▸ I.zero_mem
      have : (0 : R) = 1 := @Subsingleton.elim R h 0 1
      exact h0 (this ▸ isUnit_one)

    apply IsLocalRing.of_nonunits_add
    intro a b ha hb
    rw [← hI] at ha hb ⊢
    exact I.add_mem ha hb

end LocalRing

section RegularLocalDVR

open IsLocalRing Module

theorem regularLocalRing_dim_one_iff_dvr (R : Type*) [CommRing R] [IsDomain R] :
    (IsRegularLocalRing R ∧ ringKrullDim R = 1) ↔ IsDiscreteValuationRing R := by
  constructor
  · rintro ⟨hreg, hdim⟩
    haveI := hreg.toIsLocalRing
    haveI : IsNoetherianRing R := inferInstance
    rw [← finrank_CotangentSpace_eq_one_iff]
    have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp hreg
    exact_mod_cast hfin.trans hdim
  · intro hdvr
    refine ⟨inferInstance, ?_⟩
    exact IsPrincipalIdealRing.ringKrullDim_eq_one R
      (isField_iff_maximalIdeal_eq.not.mpr (IsDiscreteValuationRing.not_a_field R))

end RegularLocalDVR

section DVR_Noetherian

open IsLocalRing in
theorem valuationRing_noetherian_iff_dvr
    (R : Type*) [CommRing R] [IsDomain R] (hR : ¬IsField R) :
    (ValuationRing R ∧ IsNoetherianRing R) ↔ IsDiscreteValuationRing R := by
  constructor
  · rintro ⟨hV, hN⟩
    haveI := hV
    haveI := hN
    exact ((IsDiscreteValuationRing.TFAE R hR).out 1 0).mp hV
  · intro hdvr
    exact ⟨inferInstance, inferInstance⟩

end DVR_Noetherian

section LocalizationAtPrime

def localizationAtPrime (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :=
  Localization.AtPrime 𝔭

instance localizationAtPrime.isLocalRing (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    IsLocalRing (Localization.AtPrime 𝔭) :=
  inferInstance

theorem localizationAtPrime.maximalIdeal_eq (R : Type*) [CommRing R]
    (𝔭 : Ideal R) [𝔭.IsPrime] :
    IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
      𝔭.map (algebraMap R (Localization.AtPrime 𝔭)) :=
  (Localization.AtPrime.map_eq_maximalIdeal).symm

end LocalizationAtPrime

section Definition1620

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def valuationOfValuationRing :
    Valuation K (ValuationRing.ValueGroup R K) :=
  ValuationRing.valuation R K


theorem valuation_mul (x y : K) :
    ValuationRing.valuation R K (x * y) =
      ValuationRing.valuation R K x * ValuationRing.valuation R K y :=
  map_mul _ x y


noncomputable def valuationRingEquivInteger :
    R ≃+* (ValuationRing.valuation R K).integer :=
  ValuationRing.equivInteger R K

end Definition1620

section Definition1627

variable {R : Type*} [CommRing R] {k : Type*} [Field k]

def maximalIdealAtPoint (φ : R →+* k) : Ideal R := RingHom.ker φ

theorem maximalIdealAtPoint_isMaximal (φ : R →+* k) (hφ : Function.Surjective φ) :
    (maximalIdealAtPoint φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ hφ


abbrev localRingAtPoint (φ : R →+* k) [(maximalIdealAtPoint φ).IsPrime] :=
  Localization.AtPrime (maximalIdealAtPoint φ)

instance localRingAtPoint_isLocalRing (φ : R →+* k)
    [(maximalIdealAtPoint φ).IsPrime] :
    IsLocalRing (localRingAtPoint φ) :=
  inferInstance


noncomputable def quotient_maximalIdealAtPoint_ringEquiv
    (φ : R →+* k) (hφ : Function.Surjective φ) :
    R ⧸ maximalIdealAtPoint φ ≃+* k :=
  RingHom.quotientKerEquivOfSurjective hφ

def localRingAtPoint_algebraMap (φ : R →+* k)
    [(maximalIdealAtPoint φ).IsPrime] :
    R →+* localRingAtPoint φ :=
  algebraMap R (localRingAtPoint φ)


end Definition1627
