/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Spectrum

open Matrix

namespace LeastSquares

/-- For a real square matrix, the transpose equals the star (since conjugation is trivial on `ℝ`). -/
lemma transpose_eq_star_real {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : X.transpose = star X := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- Quadratic expansion: `⟨a - t·b, a - t·b⟩ = ⟨a,a⟩ - 2t⟨a,b⟩ + t²⟨b,b⟩`. -/
lemma dotProduct_sub_smul_expand {n : ℕ} (a b : Fin n → ℝ) (t : ℝ) :
    dotProduct (a - t • b) (a - t • b) =
    dotProduct a a - 2 * t * dotProduct a b + t ^ 2 * dotProduct b b := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    dotProduct_comm b a]
  ring

/-- If `-2 t a + t² b ≥ 0` for every real `t` and `b ≥ 0`, then `a = 0`. -/
lemma eq_zero_of_forall_quad_nonneg (a b : ℝ) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, -2 * t * a + t ^ 2 * b ≥ 0) : a = 0 := by
  by_contra ha
  rcases eq_or_lt_of_le hb with hb0 | hb_pos
  ·
    rw [← hb0] at h
    simp only [mul_zero, add_zero, ge_iff_le, neg_mul] at h
    have h1 := h 1
    have h2 := h (-1)
    simp only [mul_one, mul_neg_one, neg_mul] at h1 h2
    exact ha (le_antisymm (by linarith) (by linarith))
  ·
    have := h (a / b)
    have hab : -2 * (a / b) * a + (a / b) ^ 2 * b = -(a ^ 2 / b) := by
      field_simp; ring
    rw [hab] at this
    linarith [div_pos (sq_pos_of_ne_zero ha) hb_pos]

/-- The self dot product of a real vector is nonnegative. -/
lemma dotProduct_self_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ dotProduct v v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a := v i)

/-- If `θ` minimizes `‖Y - Xθ‖²` then the residual `Y - Xθ` is orthogonal to every column
of `X`, i.e. `Xᵀ (Y - Xθ) = 0`. This is the residual form of the normal equations. -/
theorem leastSquares_normalEquations_residual
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ)
    (θ : Fin d → ℝ)
    (hmin : ∀ θ' : Fin d → ℝ,
      dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :
    X.transpose *ᵥ (Y - X *ᵥ θ) = 0 := by

  set r := Y - X *ᵥ θ with hr_def

  have key : ∀ v : Fin d → ℝ, dotProduct r (X *ᵥ v) = 0 := by
    intro v

    have hmin_t : ∀ t : ℝ, dotProduct r r ≤
        dotProduct (r - t • (X *ᵥ v)) (r - t • (X *ᵥ v)) := by
      intro t
      have : Y - X *ᵥ (θ + t • v) = r - t • (X *ᵥ v) := by
        simp only [hr_def, mulVec_add, mulVec_smul]; abel
      rw [← this]
      exact hmin (θ + t • v)


    have nonneg : ∀ t : ℝ,
        -2 * t * dotProduct r (X *ᵥ v) +
        t ^ 2 * dotProduct (X *ᵥ v) (X *ᵥ v) ≥ 0 := by
      intro t
      have := hmin_t t
      rw [dotProduct_sub_smul_expand] at this
      linarith

    exact eq_zero_of_forall_quad_nonneg _ _
      (dotProduct_self_nonneg (X *ᵥ v)) nonneg


  apply dotProduct_eq_zero
  intro w
  have := key w
  rw [dotProduct_mulVec] at this
  rw [mulVec_transpose]
  exact this

/-- Normal equations: any least-squares minimizer `θ` satisfies `Xᵀ X θ = Xᵀ Y`.
This is the first part of Proposition 2.1. -/
theorem leastSquares_normalEquations
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ)
    (θ : Fin d → ℝ)
    (hmin : ∀ θ' : Fin d → ℝ,
      dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :
    X.transpose *ᵥ (X *ᵥ θ) = X.transpose *ᵥ Y := by
  have h := leastSquares_normalEquations_residual X Y θ hmin
  rw [mulVec_sub] at h
  exact (eq_of_sub_eq_zero h).symm

/-- Predicate stating that `B` is the Moore–Penrose pseudoinverse of `A`. It encodes the
four classical Penrose conditions: `A B A = A`, `B A B = B`, `A B` is symmetric, and
`B A` is symmetric. -/
structure IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop where
  mul_pinv_mul : A * B * A = A
  pinv_mul_pinv : B * A * B = B
  mul_pinv_symmetric : (A * B).transpose = A * B
  pinv_mul_symmetric : (B * A).transpose = B * A

/-- Every real matrix admits a Moore–Penrose pseudoinverse, constructed via the spectral
decomposition of `Aᵀ A`. -/
lemma exists_moorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ∃ B : Matrix n m ℝ, IsMoorePenrosePseudoinverse A B := by
  set H := A.conjTranspose * A with hH_def
  have hH : H.IsHermitian := isHermitian_conjTranspose_mul_self A
  set φ : Matrix n n ℝ ≃⋆ₐ[ℝ] Matrix n n ℝ :=
    Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hH.eigenvectorUnitary
  set D := diagonal hH.eigenvalues with hD_def
  set D_inv := diagonal (fun i => (hH.eigenvalues i)⁻¹) with hDinv_def
  set H_pinv := φ D_inv with hHpinv_def

  have hD_eq : diagonal (RCLike.ofReal ∘ hH.eigenvalues) = D := by
    simp [hD_def, RCLike.ofReal_real_eq_id]
  have hH_eq : H = φ D := by rw [hH.spectral_theorem, hD_eq]
  refine ⟨H_pinv * A.conjTranspose, ?_⟩

  have h1H : H * H_pinv * H = H := by
    rw [hH_eq, hHpinv_def, ← map_mul, ← map_mul]; congr 1
    simp only [hD_def, hDinv_def, diagonal_mul_diagonal]
    congr 1; ext i; by_cases h : hH.eigenvalues i = 0 <;> simp [h]

  have h2H : H_pinv * H * H_pinv = H_pinv := by
    rw [hH_eq, hHpinv_def, ← map_mul, ← map_mul]; congr 1
    simp only [hD_def, hDinv_def, diagonal_mul_diagonal]
    congr 1; ext i; by_cases h : hH.eigenvalues i = 0 <;> simp [h]

  have h4H : (H_pinv * H).transpose = H_pinv * H := by
    rw [hH_eq, hHpinv_def, transpose_eq_star_real, ← map_mul, ← map_star φ,
      ← transpose_eq_star_real]
    congr 1; simp only [hDinv_def, hD_def, diagonal_mul_diagonal, diagonal_transpose]

  have h_sym : H_pinv.transpose = H_pinv := by
    rw [transpose_eq_star_real, hHpinv_def, ← map_star φ, ← transpose_eq_star_real,
      hDinv_def, diagonal_transpose]

  have h_A_proj : A * H_pinv * H = A := by
    have h_ker : A * (1 - H_pinv * H) = 0 := by
      rw [← conjTranspose_mul_self_mul_eq_zero, ← hH_def,
        Matrix.mul_sub, Matrix.mul_one,
        show H * (H_pinv * H) = H * H_pinv * H from (Matrix.mul_assoc H H_pinv H).symm,
        h1H, sub_self]
    rw [Matrix.mul_sub, Matrix.mul_one] at h_ker
    rw [Matrix.mul_assoc A H_pinv H]
    exact (eq_of_sub_eq_zero h_ker).symm
  constructor

  · rw [Matrix.mul_assoc, Matrix.mul_assoc H_pinv, ← hH_def, ← Matrix.mul_assoc, h_A_proj]

  · rw [Matrix.mul_assoc H_pinv A.conjTranspose A, ← hH_def,
      ← Matrix.mul_assoc (H_pinv * H) H_pinv A.conjTranspose, h2H]

  · simp only [transpose_mul, h_sym, transpose_transpose,
      conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

  · have : H_pinv * A.conjTranspose * A = H_pinv * H := by
      rw [Matrix.mul_assoc, hH_def]
    rw [this, h4H, ← this]

/-- The Moore–Penrose pseudoinverse `A†` of a real square matrix `A`, obtained by choice
from `exists_moorePenrosePseudoinverse`. -/
noncomputable def moorePenrosePseudoinverse {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (exists_moorePenrosePseudoinverse A).choose

/-- The defining specification of `moorePenrosePseudoinverse A`: it satisfies the Penrose
conditions encoded by `IsMoorePenrosePseudoinverse`. -/
lemma moorePenrosePseudoinverse_spec {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) : IsMoorePenrosePseudoinverse A (moorePenrosePseudoinverse A) :=
  (exists_moorePenrosePseudoinverse A).choose_spec

postfix:max "†" => moorePenrosePseudoinverse

/-- The range of `Xᵀ` is contained in the range of the Gram matrix `Xᵀ X`. Equivalently,
the equation `(Xᵀ X) w = Xᵀ Y` is solvable for any `Y`. -/
theorem range_transpose_subset_range_gramian {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) :
    ∃ w : Fin d → ℝ, (X.transpose * X) *ᵥ w = X.transpose *ᵥ Y := by

  have hle : (X.transpose * X).mulVecLin.range ≤ X.transpose.mulVecLin.range := by
    intro v hv
    rw [LinearMap.mem_range] at hv ⊢
    obtain ⟨u, hu⟩ := hv
    refine ⟨X *ᵥ u, ?_⟩
    simp only [mulVecLin_apply] at hu ⊢
    rw [← hu, ← mulVec_mulVec]

  have hrank : X.transpose.rank = (X.transpose * X).rank := by
    rw [Matrix.rank_transpose, ← conjTranspose_eq_transpose_of_trivial X,
        Matrix.rank_conjTranspose_mul_self]

  have heq : (X.transpose * X).mulVecLin.range = X.transpose.mulVecLin.range :=
    Submodule.eq_of_le_of_finrank_le hle (le_of_eq hrank)

  have hmem : X.transpose *ᵥ Y ∈ X.transpose.mulVecLin.range :=
    ⟨Y, rfl⟩
  rw [← heq] at hmem
  exact hmem

/-- Converse to `leastSquares_normalEquations_residual`: any `θ` whose residual satisfies
`Xᵀ(Y - Xθ) = 0` is a minimizer of the least-squares objective. -/
theorem normalEquations_imply_minimizer
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ)
    (θ : Fin d → ℝ)
    (hresid : X.transpose *ᵥ (Y - X *ᵥ θ) = 0) :
    ∀ θ' : Fin d → ℝ,
      dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ') := by
  intro θ'
  set r := Y - X *ᵥ θ

  have decomp : Y - X *ᵥ θ' = r - X *ᵥ (θ' - θ) := by
    simp only [r, mulVec_sub]; abel
  rw [decomp]
  set v := θ' - θ

  have ortho : dotProduct r (X *ᵥ v) = 0 := by
    rw [dotProduct_mulVec,
      show vecMul r X = X.transpose *ᵥ r from by rw [mulVec_transpose],
      hresid]
    exact zero_dotProduct _

  have expand : dotProduct (r - X *ᵥ v) (r - X *ᵥ v) =
    dotProduct r r - 2 * dotProduct r (X *ᵥ v) + dotProduct (X *ᵥ v) (X *ᵥ v) := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm (X *ᵥ v) r]; ring
  rw [expand, ortho]
  linarith [dotProduct_self_nonneg (X *ᵥ v)]

/-- The candidate `(XᵀX)† Xᵀ Y` satisfies the normal equations `(XᵀX) θ = Xᵀ Y`. -/
lemma pseudoinverse_satisfies_normal_eq {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) :
    (X.transpose * X) *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)) =
    X.transpose *ᵥ Y := by
  obtain ⟨w, hw⟩ := range_transpose_subset_range_gramian X Y
  set A := X.transpose * X
  rw [← hw]

  have step1 : A† *ᵥ (A *ᵥ w) = (A† * A) *ᵥ w := by rw [mulVec_mulVec]
  rw [step1]
  have step2 : A *ᵥ ((A† * A) *ᵥ w) = (A * (A† * A)) *ᵥ w := by rw [mulVec_mulVec]
  rw [step2, ← Matrix.mul_assoc, (moorePenrosePseudoinverse_spec A).mul_pinv_mul]

/-- Closed-form least-squares estimator: `θ̂^LS := (XᵀX)† Xᵀ Y` is a minimizer of the
squared error `‖Y - Xθ‖²`. This is the second part of Proposition 2.1. -/
theorem leastSquares_pseudoinverse
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) :
    let θ_LS := (X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)
    ∀ θ' : Fin d → ℝ,
      dotProduct (Y - X *ᵥ θ_LS) (Y - X *ᵥ θ_LS) ≤
      dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ') := by
  intro θ_LS

  apply normalEquations_imply_minimizer X Y θ_LS

  rw [mulVec_sub, sub_eq_zero]

  have h : X.transpose *ᵥ (X *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y))) =
    (X.transpose * X) *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)) := by
    rw [mulVec_mulVec]
  rw [h]
  exact (pseudoinverse_satisfies_normal_eq X Y).symm

/-- Proposition 2.1 (combined form): any least-squares minimizer satisfies the normal
equations `Xᵀ X θ = Xᵀ Y`, and the pseudoinverse formula `θ̂^LS = (XᵀX)† Xᵀ Y` produces
such a minimizer. -/
theorem leastSquares_normalEquations_and_pseudoinverse
    {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) :
    (∀ (θ : Fin d → ℝ),
      (∀ θ' : Fin d → ℝ,
        dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) →
      X.transpose *ᵥ (X *ᵥ θ) = X.transpose *ᵥ Y) ∧
    (let θ_LS := (X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)
     ∀ θ' : Fin d → ℝ,
      dotProduct (Y - X *ᵥ θ_LS) (Y - X *ᵥ θ_LS) ≤
      dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :=
  ⟨fun θ hmin => leastSquares_normalEquations X Y θ hmin,
   leastSquares_pseudoinverse X Y⟩

end LeastSquares
