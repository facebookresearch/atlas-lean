/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false

namespace BilinearForms

open LinearMap LinearMap.BilinForm Module

theorem bilinearForm_matrix_correspondence {n : ℕ}
    (B : LinearMap.BilinForm ℝ (Fin n → ℝ)) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ, Matrix.toBilin' A = B) ∧
    (LinearMap.IsSymm B ↔ (BilinForm.toMatrix' B).IsSymm) := by
  constructor
  · exact ⟨BilinForm.toMatrix' B, Matrix.toBilin'_toMatrix' B⟩
  · constructor
    · intro h
      ext i j
      simp only [Matrix.transpose_apply, BilinForm.toMatrix'_apply]
      exact h.eq _ _
    · intro h
      constructor
      intro x y
      simp only [RingHom.id_apply]
      conv_lhs => rw [← Matrix.toBilin'_toMatrix' B]
      conv_rhs => rw [← Matrix.toBilin'_toMatrix' B]
      simp only [Matrix.toBilin'_apply]
      rw [Finset.sum_comm]
      congr 1
      ext i
      congr 1
      ext j
      have hM := h.apply i j
      rw [hM]
      ring

theorem orthogonal_complement_def {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (B : LinearMap.BilinForm R M) (W : Submodule R M) (v : M) :
    v ∈ B.orthogonal W ↔ ∀ w ∈ W, B.IsOrtho w v :=
  mem_orthogonal_iff

theorem nondegenerate_iff_det_ne_zero
    {A : Type*} [CommRing A] [IsDomain A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : LinearMap.BilinForm A M) (b : Basis ι A M) :
    B.Nondegenerate ↔ (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
  LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b

theorem exists_normalized_orthogonal_basis
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) :=
  QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q

theorem signature_invariance
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    {Q Q' : QuadraticForm ℝ M}
    (h : QuadraticMap.Equivalent Q Q') :
    sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' ∧
    (finrank ℝ M - sigPos Q - sigNeg Q = finrank ℝ M - sigPos Q' - sigNeg Q') := by
  exact ⟨h.sigPos_eq, h.sigNeg_eq, by rw [h.sigPos_eq, h.sigNeg_eq]⟩

end BilinearForms
