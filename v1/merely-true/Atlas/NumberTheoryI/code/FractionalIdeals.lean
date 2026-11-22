/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open nonZeroDivisors

theorem isFractional_iff_fg
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Submodule A K) :
    IsFractional A⁰ I ↔ I.FG := by
  constructor
  · intro hI
    exact FractionalIdeal.fg_of_isNoetherianRing (le_refl A⁰) ⟨I, hI⟩
  · exact FractionalIdeal.isFractional_of_fg

theorem submodule_fg_iff_isFractional
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Submodule A K) :
    I.FG ↔ IsFractional A⁰ I := by
  constructor
  · exact FractionalIdeal.isFractional_of_fg
  · intro hI
    exact FractionalIdeal.fg_of_isNoetherianRing (le_refl A⁰) ⟨I, hI⟩

theorem ideal_coe_fractionalIdeal
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Ideal A) :
    ∃ J : FractionalIdeal A⁰ K,
      (J : Submodule A K) = IsLocalization.coeSubmodule K I :=
  ⟨↑I, rfl⟩

theorem fractionalIdeal_exists_eq_spanSingleton_mul
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (J : FractionalIdeal A⁰ K) :
    ∃ (a : A) (I : Ideal A), a ≠ 0 ∧
      J = FractionalIdeal.spanSingleton A⁰ ((algebraMap A K a)⁻¹) * ↑I :=
  FractionalIdeal.exists_eq_spanSingleton_mul J

@[deprecated isFractional_iff_fg (since := "2025-05-04")]
theorem Definition_2_13
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Submodule A K) :
    IsFractional A⁰ I ↔ I.FG := isFractional_iff_fg A K I

@[deprecated submodule_fg_iff_isFractional (since := "2025-05-04")]
theorem Lemma_2_14
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Submodule A K) :
    I.FG ↔ IsFractional A⁰ I := submodule_fg_iff_isFractional A K I

@[deprecated fractionalIdeal_exists_eq_spanSingleton_mul (since := "2025-05-04")]
theorem Corollary_2_16
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (J : FractionalIdeal A⁰ K) :
    ∃ (a : A) (I : Ideal A), a ≠ 0 ∧
      J = FractionalIdeal.spanSingleton A⁰ ((algebraMap A K a)⁻¹) * ↑I :=
  fractionalIdeal_exists_eq_spanSingleton_mul A K J

section PrincipalFractionalIdeals

variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable abbrev principalFractionalIdeal (x : K) : FractionalIdeal A⁰ K :=
  FractionalIdeal.spanSingleton A⁰ x

end PrincipalFractionalIdeals

section PrincipalFractionalIdealProps

variable (A : Type*) [CommRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

theorem fractionalIdeal_isPrincipal_iff
    (I : FractionalIdeal A⁰ K) :
    (I : Submodule A K).IsPrincipal ↔ ∃ x : K, I = FractionalIdeal.spanSingleton A⁰ x :=
  FractionalIdeal.isPrincipal_iff I

@[deprecated fractionalIdeal_isPrincipal_iff (since := "2025-05-04")]
theorem Definition_2_17
    (I : FractionalIdeal A⁰ K) :
    (I : Submodule A K).IsPrincipal ↔ ∃ x : K, I = FractionalIdeal.spanSingleton A⁰ x :=
  fractionalIdeal_isPrincipal_iff A K I

theorem mem_principalFractionalIdeal (x y : K) :
    y ∈ principalFractionalIdeal A K x ↔ ∃ a : A, a • x = y :=
  FractionalIdeal.mem_spanSingleton A⁰

end PrincipalFractionalIdealProps

theorem colonIdeal_isFractional
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    IsFractional A⁰ ((I : Submodule A K) / (J : Submodule A K)) :=
  FractionalIdeal.isFractional_div_of_ne_zero hJ

@[deprecated colonIdeal_isFractional (since := "2025-05-04")]
theorem Lemma_2_18_isFractional
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    IsFractional A⁰ ((I : Submodule A K) / (J : Submodule A K)) :=
  colonIdeal_isFractional A K I J hJ

theorem colonIdeal_isFractionalIdeal
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    ∃ Q : FractionalIdeal A⁰ K,
      ∀ x : K, x ∈ (Q : Submodule A K) ↔
        ∀ y ∈ (J : Submodule A K), x * y ∈ (I : Submodule A K) :=
  ⟨I / J, fun _ => FractionalIdeal.mem_div_iff_of_ne_zero hJ⟩

@[deprecated colonIdeal_isFractionalIdeal (since := "2025-05-04")]
theorem Lemma_2_18
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    ∃ Q : FractionalIdeal A⁰ K,
      ∀ x : K, x ∈ (Q : Submodule A K) ↔
        ∀ y ∈ (J : Submodule A K), x * y ∈ (I : Submodule A K) :=
  colonIdeal_isFractionalIdeal A K I J hJ

namespace FractionalIdeal

section

variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

def IsInvertible (I : FractionalIdeal A⁰ K) : Prop :=
  ∃ J : FractionalIdeal A⁰ K, I * J = 1

omit [IsDomain A] [IsFractionRing A K] in
theorem isInvertible_iff_exists_mul_eq_one (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ ∃ J : FractionalIdeal A⁰ K, I * J = 1 :=
  Iff.rfl

omit [IsDomain A] [IsFractionRing A K] in
@[deprecated isInvertible_iff_exists_mul_eq_one (since := "2025-05-04")]
theorem Definition_2_19 (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ ∃ J : FractionalIdeal A⁰ K, I * J = 1 :=
  isInvertible_iff_exists_mul_eq_one I

theorem isInvertible_iff_mul_inv_cancel (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ I * I⁻¹ = 1 :=
  (FractionalIdeal.mul_inv_cancel_iff K).symm

theorem IsInvertible.inv_eq (I J : FractionalIdeal A⁰ K) (h : I * J = 1) :
    J = I⁻¹ :=
  FractionalIdeal.right_inverse_eq K I J h

end

section

variable {A : Type*} [CommRing A]
variable {K : Type*} [Field K] [Algebra A K]

theorem isInvertible_iff_isUnit (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ IsUnit I :=
  isUnit_iff_exists_inv.symm

theorem IsInvertible.inv_unique (I J J' : FractionalIdeal A⁰ K)
    (hJ : I * J = 1) (hJ' : I * J' = 1) : J = J' := by
  calc J = J * 1 := (mul_one J).symm
    _ = J * (I * J') := by rw [hJ']
    _ = (J * I) * J' := (mul_assoc J I J').symm
    _ = (I * J) * J' := by rw [mul_comm J I]
    _ = 1 * J' := by rw [hJ]
    _ = J' := one_mul J'

end

section

variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem isInvertible_iff_mul_inv_eq_one (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ I * I⁻¹ = 1 := by
  constructor
  ·
    rintro ⟨J, hJ⟩
    have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J hJ


    have hJ_le : J ≤ I⁻¹ := by
      rw [FractionalIdeal.inv_eq]
      exact (le_div_iff_of_ne_zero hI).mpr fun y hy x hx => by
        rw [mul_comm]; exact hJ ▸ mul_mem_mul hx hy

    apply le_antisymm
    ·
      rw [FractionalIdeal.inv_eq]; exact mul_one_div_le_one
    ·
      calc (1 : FractionalIdeal A⁰ K) = I * J := hJ.symm
        _ ≤ I * I⁻¹ := by gcongr
  ·
    exact fun h => ⟨I⁻¹, h⟩

@[deprecated isInvertible_iff_mul_inv_eq_one (since := "2025-05-04")]
theorem Lemma_2_20 (I : FractionalIdeal A⁰ K) :
    IsInvertible I ↔ I * I⁻¹ = 1 := isInvertible_iff_mul_inv_eq_one I

end

end FractionalIdeal

section IdealGroupDef

variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable abbrev IdealGroup : Type _ := (FractionalIdeal A⁰ K)ˣ

instance IdealGroup.commGroup : CommGroup (IdealGroup A K) := inferInstance

omit [IsDomain A] [IsFractionRing A K] in
theorem mem_idealGroup_iff (I : FractionalIdeal A⁰ K) :
    IsUnit I ↔ FractionalIdeal.IsInvertible I :=
  (FractionalIdeal.isInvertible_iff_isUnit I).symm

end IdealGroupDef

section IdealClassGroupDef

variable (A : Type*) [CommRing A] [IsDomain A]

noncomputable abbrev IdealClassGroup : Type _ := ClassGroup A

noncomputable instance IdealClassGroup.commGroup : CommGroup (IdealClassGroup A) := inferInstance

noncomputable abbrev PicardGroup : Type _ := IdealClassGroup A

noncomputable def IdealClassGroup.mk (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    (FractionalIdeal A⁰ K)ˣ →* IdealClassGroup A :=
  ClassGroup.mk

theorem IdealClassGroup.eq_classGroup : IdealClassGroup A = ClassGroup A := rfl

end IdealClassGroupDef
