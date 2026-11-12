/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Spectrum

open Matrix

namespace SymmetricMatrixProperties

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_iff_transpose_eq (M : Matrix n n ℝ) :
    M.IsHermitian ↔ Mᵀ = M := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]

omit [DecidableEq n] in
theorem eigenvectors_orthogonal_of_ne_eigenvalues
    {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {v w : n → ℝ} {μ₁ μ₂ : ℝ} (hμ : μ₁ ≠ μ₂)
    (hv : M.mulVec v = μ₁ • v) (hw : M.mulVec w = μ₂ • w) :
    dotProduct v w = 0 := by
  have hsym : Mᵀ = M := (isHermitian_iff_transpose_eq M).mp hM

  have symm_dot : dotProduct (M *ᵥ v) w = dotProduct v (M *ᵥ w) := by
    rw [dotProduct_comm (M *ᵥ v) w, dotProduct_mulVec]
    have hvecmul : w ᵥ* M = M *ᵥ w := by
      conv_lhs => rw [← hsym]
      exact vecMul_transpose M w
    rw [hvecmul, dotProduct_comm]

  have h1 : dotProduct (M *ᵥ v) w = μ₁ * dotProduct v w := by
    rw [hv, smul_dotProduct, smul_eq_mul]
  have h2 : dotProduct v (M *ᵥ w) = μ₂ * dotProduct v w := by
    rw [hw, dotProduct_smul, smul_eq_mul]

  have key : μ₁ * dotProduct v w = μ₂ * dotProduct v w := by linarith
  have h := sub_eq_zero.mpr key
  rw [← sub_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμ)

omit [DecidableEq n] in
theorem eigenvector_linear_combination
    {M : Matrix n n ℝ} {v w : n → ℝ} {μ : ℝ}
    (hv : M.mulVec v = μ • v) (hw : M.mulVec w = μ • w)
    (a b : ℝ) :
    M.mulVec (a • v + b • w) = μ • (a • v + b • w) := by
  rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, smul_add, smul_comm μ a, smul_comm μ b]

theorem exists_orthonormalBasis_eigenvectors (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    ∃ (v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (eigvals : n → ℝ),
      ∀ j, M.mulVec (v j) = eigvals j • (v j) :=
  ⟨hM.eigenvectorBasis, hM.eigenvalues, hM.mulVec_eigenvectorBasis⟩

theorem eq_eigenvectorUnitary_mul_diagonal_mul_transpose
    (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    M = (↑hM.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal hM.eigenvalues *
        (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  have h := hM.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  have hstar : (star (↑hM.eigenvectorUnitary : Matrix n n ℝ)) =
      (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hdiag : diagonal (RCLike.ofReal ∘ hM.eigenvalues) = diagonal hM.eigenvalues := by
    congr 1
  rw [hstar, hdiag] at h
  exact h

theorem proposition2_symmetric_matrix (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (∀ {v w : n → ℝ} {μ₁ μ₂ : ℝ}, μ₁ ≠ μ₂ →
      M.mulVec v = μ₁ • v → M.mulVec w = μ₂ • w → dotProduct v w = 0) ∧
    (∀ {v w : n → ℝ} {μ : ℝ},
      M.mulVec v = μ • v → M.mulVec w = μ • w →
      ∀ a b : ℝ, M.mulVec (a • v + b • w) = μ • (a • v + b • w)) ∧
    (∃ (v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (eigvals : n → ℝ),
      ∀ j, M.mulVec (v j) = eigvals j • (v j)) ∧
    (M = (↑hM.eigenvectorUnitary : Matrix n n ℝ) *
        Matrix.diagonal hM.eigenvalues *
        (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ) :=
  ⟨fun hμ hv hw => eigenvectors_orthogonal_of_ne_eigenvalues hM hμ hv hw,
   fun hv hw a b => eigenvector_linear_combination hv hw a b,
   exists_orthonormalBasis_eigenvectors M hM,
   eq_eigenvectorUnitary_mul_diagonal_mul_transpose M hM⟩

end SymmetricMatrixProperties
