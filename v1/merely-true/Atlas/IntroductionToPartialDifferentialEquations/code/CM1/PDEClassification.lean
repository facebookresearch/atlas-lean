/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Finset

namespace PDEClassification

/-- Hadamard's classification of second-order linear PDEs into elliptic, hyperbolic, and
parabolic types, determined by the signature of the leading symbol matrix. -/
inductive PDEType where
  | elliptic
  | hyperbolic
  | parabolic
  deriving DecidableEq, Repr

variable {N : Type*} [Fintype N] [DecidableEq N]

section Classification

variable {A : Matrix N N ℝ} (hA : A.IsHermitian)

/-- $A$ is elliptic iff all eigenvalues of $A$ are strictly positive, or all are strictly
negative — i.e. the leading-symbol matrix is definite. -/
def IsElliptic : Prop :=
  (∀ i, 0 < hA.eigenvalues i) ∨ (∀ i, hA.eigenvalues i < 0)

/-- $A$ is hyperbolic iff all eigenvalues are nonzero and there exists an index $j$ such
that every other eigenvalue has sign opposite to that of $\lambda_j$ (signature
$(1, n-1)$ or $(n-1, 1)$). -/
def IsHyperbolic : Prop :=
  (∀ i, hA.eigenvalues i ≠ 0) ∧
  (∃ j, ∀ i, i ≠ j → hA.eigenvalues i * hA.eigenvalues j < 0)

/-- $A$ is parabolic iff there is exactly one zero eigenvalue (at some index $j$) and all
other eigenvalues are nonzero and share a common sign (their pairwise products are
positive). -/
def IsParabolic : Prop :=
  ∃ j, hA.eigenvalues j = 0 ∧
    (∀ i, i ≠ j → hA.eigenvalues i ≠ 0) ∧
    (∀ i₁ i₂, i₁ ≠ j → i₂ ≠ j → 0 < hA.eigenvalues i₁ * hA.eigenvalues i₂)

end Classification

section NormalForms

variable (n : ℕ)

end NormalForms

/-- Spectral theorem (real-symmetric form): for a real Hermitian matrix $A$ with the
orthogonal matrix $U$ of eigenvectors, $U^{T} A U = \operatorname{diag}(\lambda_i)$. -/
theorem spectral_diagonalization {A : Matrix N N ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ * A * (hA.eigenvectorUnitary : Matrix N N ℝ)
      = Matrix.diagonal hA.eigenvalues := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_apply] at h
  have hstar_eq : star (hA.eigenvectorUnitary : Matrix N N ℝ) =
      (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ := by
    ext i j; simp [star_apply, star_trivial]
  rw [← hstar_eq]
  exact h

/-- The matrix of eigenvectors produced by the spectral theorem is invertible
(nonzero determinant), as it is orthogonal. -/
theorem eigenvectorUnitary_det_ne_zero {A : Matrix N N ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix N N ℝ).det ≠ 0 := by
  intro hdet
  have hU := (hA.eigenvectorUnitary).prop
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  have h1 : (1 : Matrix N N ℝ).det = 0 := by
    rw [← hU, det_mul]
    have : star (hA.eigenvectorUnitary : Matrix N N ℝ) =
        (hA.eigenvectorUnitary : Matrix N N ℝ)ᵀ := by
      ext i j; simp [star_apply, star_trivial]
    rw [this, det_transpose, hdet, mul_zero]
  simp at h1

/-- Sign trichotomy for nonzero reals: $x \neq 0$ implies $x < 0$ or $0 < x$. -/
lemma ne_zero_lt_or_gt {x : ℝ} (hx : x ≠ 0) : x < 0 ∨ 0 < x := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inl h
  · exact absurd h hx
  · exact Or.inr h

/-- Normal form for a real Hermitian matrix: there is an invertible $M$ with $M^T A M$ a
diagonal matrix whose entries are $+1$, $-1$, or $0$ according to the sign of the
corresponding eigenvalue. This is the matrix-level statement behind Hadamard's
classification of second-order PDEs. -/
theorem classification_normal_form [Nonempty N]
    {A : Matrix N N ℝ} (hA : A.IsHermitian) :
    ∃ M : Matrix N N ℝ, M.det ≠ 0 ∧
      Mᵀ * A * M = Matrix.diagonal (fun i =>
        if 0 < hA.eigenvalues i then (1 : ℝ)
        else if hA.eigenvalues i < 0 then (-1 : ℝ)
        else (0 : ℝ)) := by
  let P : Matrix N N ℝ := hA.eigenvectorUnitary
  let scale : N → ℝ := fun i =>
    if 0 < hA.eigenvalues i then 1 / Real.sqrt (hA.eigenvalues i)
    else if hA.eigenvalues i < 0 then 1 / Real.sqrt (-(hA.eigenvalues i))
    else 1
  let S : Matrix N N ℝ := Matrix.diagonal scale
  refine ⟨P * S, ?_, ?_⟩
  ·
    rw [det_mul]
    apply mul_ne_zero (eigenvectorUnitary_det_ne_zero hA)
    rw [det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simp only [scale]
    split_ifs with h1 h2
    · exact div_ne_zero one_ne_zero (Real.sqrt_ne_zero'.mpr h1)
    · exact div_ne_zero one_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr h2))
    · exact one_ne_zero
  ·
    have key : (P * S)ᵀ * A * (P * S) = Sᵀ * (Pᵀ * A * P) * S := by
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [key, spectral_diagonalization hA, diagonal_transpose]
    simp only [S]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext i; simp only [scale]
    split_ifs with h1 h2
    ·
      field_simp; rw [Real.sq_sqrt (le_of_lt h1)]
    ·
      have hne : Real.sqrt (-hA.eigenvalues i) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (neg_pos.mpr h2)
      field_simp
      rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr h2))]
      linarith
    ·
      push Not at h1 h2
      have h0 : hA.eigenvalues i = 0 := le_antisymm h1 h2
      simp [h0]

/-- Helper: when all eigenvalues are positive, the sign-diagonal $\operatorname{diag}(\pm 1, 0)$
collapses to the identity matrix. -/
lemma sign_diagonal_eq_one {A : Matrix N N ℝ} (hA : A.IsHermitian)
    (hpos : ∀ i, 0 < hA.eigenvalues i) :
    Matrix.diagonal (fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)) = 1 := by
  ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]
  have hi := hpos i
  split_ifs with hij
  · subst hij; simp
  · rfl

/-- Helper: when all eigenvalues are negative, the sign-diagonal collapses to $-I$. -/
lemma sign_diagonal_eq_neg_one {A : Matrix N N ℝ} (hA : A.IsHermitian)
    (hneg : ∀ i, hA.eigenvalues i < 0) :
    Matrix.diagonal (fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)) = -1 := by
  ext i j
  have hi := hneg i
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq,
      not_lt.mpr hi.le, ite_false, hi, ite_true]
  · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, Matrix.one_apply_ne hij,
      neg_zero]

/-- Helper: at a nonzero eigenvalue, the sign expression evaluates to either $+1$ or $-1$. -/
lemma sign_of_ne_zero {A : Matrix N N ℝ} (hA : A.IsHermitian) {i : N}
    (hi : hA.eigenvalues i ≠ 0) :
    (if 0 < hA.eigenvalues i then (1 : ℝ)
     else if hA.eigenvalues i < 0 then (-1 : ℝ)
     else (0 : ℝ)) = 1 ∨
    (if 0 < hA.eigenvalues i then (1 : ℝ)
     else if hA.eigenvalues i < 0 then (-1 : ℝ)
     else (0 : ℝ)) = -1 := by
  rcases ne_zero_lt_or_gt hi with h | h
  · simp [not_lt.mpr h.le, h]
  · simp [h]

/-- Hadamard's classification of second-order PDEs (Theorem 3.1, matrix form): for any
real Hermitian leading-symbol matrix $A$, there exists an invertible change of variables $M$
bringing $A$ into a diagonal sign normal form, and additionally
- in the elliptic case, $M^T A M = \pm I$,
- in the hyperbolic case, $M^T A M$ is a $\pm 1$-diagonal whose entries split in sign with
  exactly one differing sign,
- in the parabolic case, $M^T A M$ is a diagonal with exactly one $0$ entry and the
  remaining entries all $+1$ or all $-1$. -/
theorem classification_theorem_3_1 [Nonempty N]
    {A : Matrix N N ℝ} (hA : A.IsHermitian) :
    ∃ M : Matrix N N ℝ, M.det ≠ 0 ∧
      Mᵀ * A * M = Matrix.diagonal (fun i =>
        if 0 < hA.eigenvalues i then (1 : ℝ)
        else if hA.eigenvalues i < 0 then (-1 : ℝ)
        else (0 : ℝ)) ∧
      ((IsElliptic hA →
          (Mᵀ * A * M = 1 ∨ Mᵀ * A * M = -1)) ∧
       (IsHyperbolic hA →
          ∃ σ : N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
            (∃ j, ∀ i, i ≠ j → σ i * σ j < 0) ∧
            Mᵀ * A * M = Matrix.diagonal σ) ∧
       (IsParabolic hA →
          ∃ j₀, ∃ σ : N → ℝ,
            σ j₀ = 0 ∧
            (∀ i, i ≠ j₀ → σ i = 1 ∨ σ i = -1) ∧
            (∀ i₁ i₂, i₁ ≠ j₀ → i₂ ≠ j₀ → σ i₁ = σ i₂) ∧
            Mᵀ * A * M = Matrix.diagonal σ)) := by
  obtain ⟨M, hM_det, hM_eq⟩ := classification_normal_form hA
  refine ⟨M, hM_det, hM_eq, ?_, ?_, ?_⟩
  ·
    intro hE
    rcases hE with hpos | hneg
    · exact Or.inl (hM_eq.symm ▸ sign_diagonal_eq_one hA hpos)
    · exact Or.inr (hM_eq.symm ▸ sign_diagonal_eq_neg_one hA hneg)
  ·

    intro hH
    let σ : N → ℝ := fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)
    refine ⟨σ, ?_, ?_, hM_eq⟩
    · intro i
      exact sign_of_ne_zero hA (hH.1 i)
    · obtain ⟨j, hj⟩ := hH.2
      refine ⟨j, fun i hi => ?_⟩
      simp only [σ]
      rcases ne_zero_lt_or_gt (hH.1 j) with hj_neg | hj_pos
      · have hi_pos : 0 < hA.eigenvalues i := by
          rcases ne_zero_lt_or_gt (hH.1 i) with hi_neg | hi_pos
          · exfalso; linarith [mul_pos_of_neg_of_neg hi_neg hj_neg, hj i hi]
          · exact hi_pos
        simp [hi_pos, not_lt.mpr hj_neg.le, hj_neg]
      · have hi_neg : hA.eigenvalues i < 0 := by
          rcases ne_zero_lt_or_gt (hH.1 i) with hi_neg | hi_pos
          · exact hi_neg
          · exfalso; linarith [mul_pos hi_pos hj_pos, hj i hi]
        simp [not_lt.mpr hi_neg.le, hi_neg, hj_pos]
  ·
    intro hP
    obtain ⟨j₀, hj₀_zero, hj₀_nonzero, hj₀_same_sign⟩ := hP
    let σ : N → ℝ := fun i =>
      if 0 < hA.eigenvalues i then (1 : ℝ)
      else if hA.eigenvalues i < 0 then (-1 : ℝ)
      else (0 : ℝ)
    refine ⟨j₀, σ, ?_, ?_, ?_, hM_eq⟩
    · simp only [σ, hj₀_zero, lt_irrefl, ↓reduceIte]
    · intro i hi
      exact sign_of_ne_zero hA (hj₀_nonzero i hi)
    · intro i₁ i₂ hi₁ hi₂; simp only [σ]
      have h_prod := hj₀_same_sign i₁ i₂ hi₁ hi₂
      rcases ne_zero_lt_or_gt (hj₀_nonzero i₁ hi₁) with h1_neg | h1_pos
      · have h2_neg : hA.eigenvalues i₂ < 0 := by
          rcases ne_zero_lt_or_gt (hj₀_nonzero i₂ hi₂) with h2_neg | h2_pos
          · exact h2_neg
          · exfalso; linarith [mul_neg_of_neg_of_pos h1_neg h2_pos]
        simp [not_lt.mpr h1_neg.le, not_lt.mpr h2_neg.le, h1_neg, h2_neg]
      · have h2_pos : 0 < hA.eigenvalues i₂ := by
          rcases ne_zero_lt_or_gt (hj₀_nonzero i₂ hi₂) with h2_neg | h2_pos
          · exfalso; linarith [mul_neg_of_pos_of_neg h1_pos h2_neg]
          · exact h2_pos
        simp [h1_pos, h2_pos]

end PDEClassification
