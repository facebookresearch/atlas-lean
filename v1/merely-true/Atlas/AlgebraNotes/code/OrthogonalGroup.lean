/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace OrthogonalGroup

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

attribute [local instance] starRingOfComm

instance orthogonalGroup_group : Group (Matrix.orthogonalGroup n R) := inferInstance

def toGL : Matrix.orthogonalGroup n R →* Matrix.GeneralLinearGroup n R :=
  Unitary.toUnits

def orthogonalSubgroup (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup n R) :=
  @MonoidHom.range _ _ (_) _ (toGL (n := n) (R := R))

def specialOrthogonalSubgroup : Subgroup (Matrix.orthogonalGroup n ℝ) where
  carrier := {A | (A : Matrix n n ℝ).det = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Submonoid.coe_mul, Matrix.det_mul] at *
    rw [ha, hb, one_mul]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Submonoid.coe_one, Matrix.det_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [show (↑(a⁻¹) : Matrix n n ℝ).det = (star (a : Matrix n n ℝ)).det from by
      rw [← Matrix.UnitaryGroup.inv_val]]
    have : star (a : Matrix n n ℝ) = (a : Matrix n n ℝ).conjTranspose := rfl
    rw [this, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose]
    exact ha
