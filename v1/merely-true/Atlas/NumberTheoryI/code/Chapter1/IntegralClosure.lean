/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

section IntegralElements


abbrev isIntegral_def (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) : Prop := IsIntegral A b

abbrev integralClosureSubalgebra (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    Subalgebra A B := integralClosure A B

end IntegralElements

theorem isIntegral_add_and_mul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {α β : B} (hα : IsIntegral A α) (hβ : IsIntegral A β) :
    IsIntegral A (α + β) ∧ IsIntegral A (α * β) :=
  ⟨hα.add hβ, hα.mul hβ⟩

theorem proposition_1_20 {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Algebra.IsIntegral A B) (hBC : Algebra.IsIntegral B C) :
    Algebra.IsIntegral A C := by
  exact Algebra.IsIntegral.trans B

theorem corollary_1_21' (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    IsIntegrallyClosedIn (integralClosure A B) B := inferInstance

theorem proposition_1_22 : IsIntegrallyClosed ℤ := inferInstance

theorem corollary_1_23 (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] :
    IsIntegrallyClosed A := inferInstance

theorem proposition_1_25 (A : Type*) [CommRing A] [IsDomain A] [ValuationRing A] :
    IsIntegrallyClosed A := inferInstance

theorem proposition_1_28 {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {α : L} (hα : IsAlgebraic K α) :
    IsIntegral A α ↔ ∀ i, (minpoly K α).coeff i ∈ (algebraMap A K).range := by
  constructor
  ·

    intro hInt
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hInt]
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  ·

    intro hcoeff
    have hlift : minpoly K α ∈ Polynomial.lifts (algebraMap A K) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff
    have hmonic : (minpoly K α).Monic := minpoly.monic hα.isIntegral
    obtain ⟨q, hq_map, _, hq_monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmonic
    have hq_root : Polynomial.aeval α q = 0 := by
      have h : Polynomial.aeval α (q.map (algebraMap A K)) = 0 := by
        rw [hq_map]; exact minpoly.aeval K α
      rwa [Polynomial.aeval_map_algebraMap (R := A) (A := K)] at h
    exact ⟨q, hq_monic, hq_root⟩
