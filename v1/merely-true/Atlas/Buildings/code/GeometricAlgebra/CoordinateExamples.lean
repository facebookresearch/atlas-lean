/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block

open Matrix

namespace CoordinateExamples

/-- The standard symplectic form matrix on `kⁿ ⊕ kⁿ`: the block matrix
`[[0, -1], [1, 0]]`. -/
noncomputable def symplecticFormMatrix (n : ℕ) (k : Type*) [Ring k] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The standard split-orthogonal (hyperbolic) form matrix on `kⁿ ⊕ kⁿ`: the
block matrix `[[0, 1], [1, 0]]`. -/
def splitOrthogonalFormMatrix (n : ℕ) (k : Type*) [Zero k] [One k] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.fromBlocks 0 1 1 0

/-- The standard signature `(p, q)` orthogonal form matrix: the block-diagonal
matrix with `1`'s in the first `p` slots and `-1`'s in the last `q` slots. -/
noncomputable def orthogonalFormMatrix (p q : ℕ) (k : Type*) [Ring k] :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) k :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- A matrix `g` is form-preserving for the bilinear form matrix `F` when
`gᵀ F g = F`. -/
def IsFormPreserving {m : ℕ} {k : Type*} [CommRing k]
    (F g : Matrix (Fin m) (Fin m) k) : Prop :=
  g.transpose * F * g = F

/-- Symplectic condition: `g` preserves the (alternating) form `J`. -/
abbrev IsSymplectic {n : ℕ} {k : Type*} [CommRing k]
    (J : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k) : Prop :=
  IsFormPreserving J g

/-- Split-orthogonal condition: `g` preserves the (symmetric hyperbolic) form `S`. -/
abbrev IsSplitOrthogonal {n : ℕ} {k : Type*} [CommRing k]
    (S : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k) : Prop :=
  IsFormPreserving S g

/-- `(p, q)`-orthogonal condition: `g` preserves the signature `(p, q)` form `Q`. -/
abbrev IsOrthogonalPQ {m : ℕ} {k : Type*} [CommRing k]
    (Q : Matrix (Fin m) (Fin m) k) (g : Matrix (Fin m) (Fin m) k) : Prop :=
  IsFormPreserving Q g

/-- A matrix `g` is an invertible isometry of the bilinear form `F` when it is
invertible (its determinant is a unit) and form-preserving (`gᵀ F g = F`). -/
def IsInvertibleIsometry {m : ℕ} {k : Type*} [CommRing k]
    (F : Matrix (Fin m) (Fin m) k) (g : Matrix (Fin m) (Fin m) k) : Prop :=
  IsUnit g.det ∧ g.transpose * F * g = F

/-- The matrix isometry group of a bilinear form matrix `J`: the subgroup of
`GL ι k` consisting of matrices `g` satisfying `gᵀ J g = J`. -/
def MatrixIsometryGroup {ι : Type*} [DecidableEq ι] [Fintype ι]
    {k : Type*} [CommRing k] (J : Matrix ι ι k) : Subgroup (GL ι k) where
  carrier := {g | g.val.transpose * J * g.val = J}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    show (a * b).val.transpose * J * (a * b).val = J
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc b.val.transpose * a.val.transpose * J * (a.val * b.val)
        = b.val.transpose * (a.val.transpose * J * a.val) * b.val := by
          simp [Matrix.mul_assoc]
      _ = b.val.transpose * J * b.val := by rw [ha]
      _ = J := hb
  one_mem' := by simp [Set.mem_setOf_eq, Units.val_one, Matrix.transpose_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : a.val * a⁻¹.val = 1 := a.val_inv
    have h3 : a⁻¹.val.transpose * a.val.transpose = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc a⁻¹.val.transpose * J * a⁻¹.val
        = a⁻¹.val.transpose * (a.val.transpose * J * a.val) * a⁻¹.val := by rw [ha]
      _ = (a⁻¹.val.transpose * a.val.transpose) * J * (a.val * a⁻¹.val) := by
          simp [Matrix.mul_assoc]
      _ = 1 * J * 1 := by rw [h3, h1]
      _ = J := by simp

/-- The symplectic group `Sp(2n, k)`: the matrix isometry group of the standard
symplectic form on `kⁿ ⊕ kⁿ`. -/
noncomputable def Sp (n : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin n ⊕ Fin n) k) :=
  MatrixIsometryGroup (symplecticFormMatrix n k)

/-- The split-orthogonal group `O(n, n; k)`: the matrix isometry group of the
standard hyperbolic symmetric form on `kⁿ ⊕ kⁿ`. -/
def OrthoSplit (n : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin n ⊕ Fin n) k) :=
  MatrixIsometryGroup (splitOrthogonalFormMatrix n k)

/-- The orthogonal group `O(p, q; k)` of signature `(p, q)`: the matrix isometry
group of the standard `(p, q)`-form on `kᵖ ⊕ kᵠ`. -/
noncomputable def OrthogonalPQ (p q : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin p ⊕ Fin q) k) :=
  MatrixIsometryGroup (orthogonalFormMatrix p q k)

/-- Combinatorial data for a standard parabolic subgroup of `GL(n)`: a list of
positive block sizes whose sum is at most `n`, used to record the dimensions of
a partial flag of subspaces. -/
structure StandardParabolicData (n : ℕ) where
  sizes : List ℕ
  sizes_pos : ∀ s ∈ sizes, 0 < s
  sizes_sum : sizes.sum ≤ n

/-- The identity matrix is form-preserving for any bilinear form matrix `F`. -/
theorem isFormPreserving_one {m : ℕ} {k : Type*} [CommRing k]
    (F : Matrix (Fin m) (Fin m) k) : IsFormPreserving F 1 := by
  unfold IsFormPreserving
  simp [Matrix.transpose_one]

end CoordinateExamples
