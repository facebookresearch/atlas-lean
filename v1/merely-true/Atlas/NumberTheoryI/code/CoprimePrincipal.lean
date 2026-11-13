/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup

open Ideal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]

theorem Ideal.exists_coprime_mul_principal (I I' : Ideal A) (hI : I ≠ ⊥) (hI' : I' ≠ ⊥) :
    ∃ J : Ideal A, J ⊔ I' = ⊤ ∧ Submodule.IsPrincipal (I * J) := by

  have hle : I * I' ≤ I := Ideal.mul_le_right

  have hne : I * I' ≠ ⊥ := mul_ne_zero hI hI'

  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne

  have ha_le : Ideal.span {a} ≤ I := by rw [← ha]; exact le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ha_le
  refine ⟨J, ?_, ?_⟩
  ·

    have h1 : I * (I' ⊔ J) = I * ⊤ := by
      rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, ha]
    have h2 : I' ⊔ J = ⊤ := mul_left_cancel₀ hI h1
    rw [sup_comm]
    exact h2
  ·
    rw [← hJ]
    exact ⟨⟨a, rfl⟩⟩

theorem ClassGroup.exists_mk0_coprime (c : ClassGroup A) (𝔞 : Ideal A) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (K : Ideal A) (hK : K ≠ ⊥),
      ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK⟩ = c ∧ K ⊔ 𝔞 = ⊤ := by

  obtain ⟨⟨J, hJ_mem⟩, hJ_class⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ_ne : J ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hJ_mem

  obtain ⟨K, hK_coprime, hK_principal⟩ := Ideal.exists_coprime_mul_principal J 𝔞 hJ_ne h𝔞
  by_cases hK_ne : K = ⊥
  ·
    have h𝔞_top : 𝔞 = ⊤ := by rw [← hK_coprime, hK_ne, bot_sup_eq]
    obtain ⟨⟨K', hK'_mem⟩, hK'_class⟩ := ClassGroup.mk0_surjective c
    have hK'_ne : K' ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hK'_mem
    exact ⟨K', hK'_ne, hK'_class, by rw [h𝔞_top, sup_top_eq]⟩
  ·


    refine ⟨K, hK_ne, ?_, hK_coprime⟩
    have hJK_ne : J * K ≠ ⊥ := mul_ne_zero hJ_ne hK_ne
    have h1 : ClassGroup.mk0 ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ = 1 := by
      rwa [ClassGroup.mk0_eq_one_iff]
    have h2 : ClassGroup.mk0 ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ =
      ClassGroup.mk0 ⟨J, hJ_mem⟩ *
        ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩ := by
      rw [← MonoidHom.map_mul]; congr 1
    rw [h2, hJ_class] at h1
    exact (eq_of_inv_mul_eq_one h1).symm
