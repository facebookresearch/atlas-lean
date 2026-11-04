/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open Module Ideal

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

noncomputable def discrIdeal (A : Type*) (B : Type*)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.spanNorm A (differentIdeal A B)

section DifferentDiscriminantTransitivity

set_option linter.unusedSectionVars false

variable (A : Type*) (B : Type*) (C : Type*)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [IsDedekindDomain C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
  [Module.IsTorsionFree A B] [Module.IsTorsionFree A C] [Module.IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)]

theorem different_tower :
    differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) :=
  differentIdeal_eq_differentIdeal_mul_differentIdeal A B C

theorem discr_tower :
    discrIdeal A C =
      (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) *
        Ideal.spanNorm A (discrIdeal B C) := by

  haveI : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)
  haveI : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing B) (FractionRing C)

  unfold discrIdeal

  rw [spanNorm_eq A (differentIdeal A C)]

  have h := different_tower A B C
  conv_lhs => rw [h]

  rw [map_mul, mul_comm]
  congr 1
  ·

    rw [← relNorm_relNorm A B (Ideal.map (algebraMap B C) (differentIdeal A B))]

    rw [relNorm_algebraMap C (differentIdeal A B)]

    rw [map_pow]

    rw [← spanNorm_eq A (differentIdeal A B)]
  ·

    rw [← relNorm_relNorm A B (differentIdeal B C)]

    rw [← spanNorm_eq B (differentIdeal B C)]
    rw [← spanNorm_eq A (spanNorm B (differentIdeal B C))]

theorem proposition_12_28 :
    (differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C)) ∧
    (discrIdeal A C = (discrIdeal A B) ^ (finrank (FractionRing B) (FractionRing C)) *
      Ideal.spanNorm A (discrIdeal B C)) :=
  ⟨different_tower A B C, discr_tower A B C⟩

end DifferentDiscriminantTransitivity
