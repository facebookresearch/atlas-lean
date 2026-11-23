/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.ClassNumber

namespace IdealFactorization

open UniqueFactorizationMonoid NumberField

instance numberField_ringOfIntegers_ideal_ufm (K : Type*) [Field K] [NumberField K] :
    UniqueFactorizationMonoid (Ideal (NumberField.RingOfIntegers K)) :=
  inferInstance

theorem numberField_ideal_factorization (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    (∀ P ∈ normalizedFactors I, Prime P) ∧
    Associated (normalizedFactors I).prod I :=
  ⟨fun P hP => prime_of_normalized_factor P hP, prod_normalizedFactors hI⟩

noncomputable def idealNorm {d : ℤ} [IsDomain (ℤ√d)] [IsDedekindDomain (ℤ√d)]
    [Module.Free ℤ (ℤ√d)] (I : Ideal (ℤ√d)) : ℕ :=
  Ideal.absNorm I

theorem ideal_mul_properties {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] :

    (∀ (I I' J : Ideal R), J ≠ ⊥ → I * J = I' * J → I = I') ∧

    (∀ (I J : Ideal R), I ≤ J → ∃ J' : Ideal R, I = J * J') := by
  constructor
  ·
    intro I I' J hJ h
    have h' : J * I = J * I' := by rw [mul_comm, h, mul_comm]
    exact mul_left_cancel₀ hJ h'
  ·
    intro I J hIJ
    have hdvd : J ∣ I := Ideal.dvd_iff_le.mpr hIJ
    obtain ⟨J', hJ'⟩ := hdvd
    exact ⟨J', hJ'⟩

theorem ideal_is_lattice {R : Type*} [CommRing R] [IsDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (I : Ideal R) (hI : I ≠ ⊥) :
    Module.Free ℤ I ∧ Module.Finite ℤ I ∧ Module.finrank ℤ I = Module.finrank ℤ R := by
  have b := Module.Free.chooseBasis ℤ R
  have hbasis := Submodule.basisOfPid b (I.restrictScalars ℤ)
  refine ⟨Module.Free.of_basis hbasis.2, Module.Finite.of_basis hbasis.2, ?_⟩
  have hfin : Finite (R ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  exact (Submodule.finiteQuotient_iff (I.restrictScalars ℤ)).mp hfin

instance classGroup_finite (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) :=
  inferInstance

def IdealsSimilar {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (I J : Ideal R) : Prop :=
  ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ Ideal.span {a} * I = Ideal.span {b} * J

theorem similar_mul_right {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I I' J : Ideal R}
    (h : IdealsSimilar I I') :
    IdealsSimilar (I * J) (I' * J) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨a, b, ha, hb, by rw [← mul_assoc, ← mul_assoc, hab]⟩

end IdealFactorization
