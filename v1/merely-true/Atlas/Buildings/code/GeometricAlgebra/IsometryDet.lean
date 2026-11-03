/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Commute

namespace Garrett

open Matrix

/-- A matrix isometry of a nondegenerate quadratic form (`gᵀ Q g = Q`) has
determinant equal to `+1` or `-1`. -/
theorem isometry_det_eq_one_or_neg_one
    {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Q g : Matrix n n R}
    (hQ : Q.det ≠ 0) (hiso : g.transpose * Q * g = Q) :
    g.det = 1 ∨ g.det = -1 := by

  have h1 : (g.transpose * Q * g).det = Q.det := by rw [hiso]
  rw [det_mul, det_mul, det_transpose] at h1


  have h2 : g.det ^ 2 * Q.det = Q.det := by
    have : g.det * Q.det * g.det = g.det ^ 2 * Q.det := by ring
    rw [← this]; exact h1

  have h3 : (g.det ^ 2 - 1) * Q.det = 0 := by
    have : (g.det ^ 2 - 1) * Q.det = g.det ^ 2 * Q.det - Q.det := by ring
    rw [this, h2, sub_self]

  have h4 : g.det ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp h3).resolve_right hQ

  have h5 : g.det ^ 2 = 1 := by
    have : g.det ^ 2 = g.det ^ 2 - 1 + 1 := by ring
    rw [this, h4, zero_add]
  exact sq_eq_one_iff.mp h5

/-- Square of the determinant of a matrix isometry of a nondegenerate quadratic
form is `1`. -/
theorem isometry_det_sq_eq_one
    {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {Q g : Matrix n n R}
    (hQ : Q.det ≠ 0) (hiso : g.transpose * Q * g = Q) :
    g.det ^ 2 = 1 := by
  rcases isometry_det_eq_one_or_neg_one hQ hiso with h | h <;> simp [h]

end Garrett
