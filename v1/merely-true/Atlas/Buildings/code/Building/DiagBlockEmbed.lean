/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.IwahoriGLnHelpers

set_option maxHeartbeats 400000

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section DiagBlockEmbed

variable {n : ℕ}

/-- The $1 \times 1$ matrix whose single entry is the scalar $a \in k$. -/
noncomputable def scalarMat1 (a : C.k) : Matrix (Fin 1) (Fin 1) C.k :=
  Matrix.of fun _ _ => a

/-- Every entry of the $1 \times 1$ scalar matrix equals $a$. -/
@[simp] lemma scalarMat1_apply (a : C.k) (i j : Fin 1) : scalarMat1 C a i j = a := by
  simp [scalarMat1, Matrix.of_apply]

/-- The block-diagonal matrix $\mathrm{diag}(a, A)$ of size $(n+1) \times
(n+1)$, putting the scalar $a$ in the top-left corner and the matrix $A$ in
the bottom-right block. -/
noncomputable def diagBlockEmbedMatrix (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) C.k :=
  (reindexAlgEquiv C.k C.k (finBlockEquiv n))
    (fromBlocks (scalarMat1 C a) 0 0 A)

/-- The $(0,0)$ entry of $\mathrm{diag}(a, A)$ is $a$. -/
@[simp]
lemma diagBlockEmbedMatrix_zero_zero (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) :
    diagBlockEmbedMatrix C a A 0 0 = a := by
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, fromBlocks_apply₁₁, scalarMat1_apply]

/-- Top row, non-corner entries of $\mathrm{diag}(a, A)$ are zero. -/
@[simp]
lemma diagBlockEmbedMatrix_zero_succ (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) (k : Fin n) :
    diagBlockEmbedMatrix C a A 0 ⟨k.val + 1, by omega⟩ = 0 := by
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₁₂, Matrix.zero_apply]

/-- Leftmost column, non-corner entries of $\mathrm{diag}(a, A)$ are zero. -/
@[simp]
lemma diagBlockEmbedMatrix_succ_zero (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) (k : Fin n) :
    diagBlockEmbedMatrix C a A ⟨k.val + 1, by omega⟩ 0 = 0 := by
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The bottom-right $n \times n$ block of $\mathrm{diag}(a, A)$ is $A$. -/
@[simp]
lemma diagBlockEmbedMatrix_succ_succ (a : C.k) (A : Matrix (Fin n) (Fin n) C.k) (k l : Fin n) :
    diagBlockEmbedMatrix C a A ⟨k.val + 1, by omega⟩ ⟨l.val + 1, by omega⟩ = A k l := by
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_succ, fromBlocks_apply₂₂]

/-- The diagonal block embedding $\mathrm{GL}_n(k) \hookrightarrow
\mathrm{GL}_{n+1}(k)$ sending $M$ to $\mathrm{diag}(a, M)$, with $a \in
k^\times$ in the leading slot. -/
noncomputable def diagBlockEmbedGL (a : C.kˣ) (M : GL (Fin n) C.k) : GL (Fin (n + 1)) C.k := by
  refine ⟨
    diagBlockEmbedMatrix C a.val M.val,
    diagBlockEmbedMatrix C (a.val)⁻¹ M.inv,
    ?_, ?_⟩
  ·
    simp only [diagBlockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    have hscal : scalarMat1 C a.val * scalarMat1 C (a.val)⁻¹ = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
    simp [hscal, fromBlocks_one]
  ·
    simp only [diagBlockEmbedMatrix]
    rw [← reindexAlgEquiv_mul, fromBlocks_multiply]
    have hscal : scalarMat1 C (a.val)⁻¹ * scalarMat1 C a.val = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
    simp [hscal, fromBlocks_one]

/-- The underlying matrix of $\mathrm{diag}(a, M)$ as a $\mathrm{GL}_{n+1}$
element coincides with the matrix-level diagonal block embedding. -/
@[simp]
theorem diagBlockEmbedGL_val (a : C.kˣ) (M : GL (Fin n) C.k) :
    (diagBlockEmbedGL C a M).val = diagBlockEmbedMatrix C a.val M.val :=
  rfl

/-- The diagonal block embedding sends diagonal matrices to diagonal matrices. -/
theorem diagBlockEmbed_preserves_diag (a : C.kˣ) (M : GL (Fin n) C.k)
    (hM : M ∈ DiagGLn C n) :
    diagBlockEmbedGL C a M ∈ DiagGLn C (n + 1) := by
  intro p q hpq
  rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
  · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
    · exact absurd rfl hpq
    · simp
  · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
    · simp
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
      exact hM k l (by intro h; apply hpq; subst h; rfl)

/-- The diagonal block embedding sends the Iwahori subgroup $I_n$ into the
Iwahori subgroup $I_{n+1}$, provided the leading scalar $a$ is a unit of
$\mathcal{O}$. -/
theorem diagBlockEmbed_preserves_iwahori (a : C.kˣ) (M : GL (Fin n) C.k)
    (ha : C.isUnitInO a.val) (hM : M ∈ IwahoriGLn C n) :
    diagBlockEmbedGL C a M ∈ IwahoriGLn C (n + 1) := by
  obtain ⟨hdiag, habove, hbelow⟩ := hM
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_zero]; exact ha
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]; exact hdiag k
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_succ]; exact DVRClosure.isInO_zero
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)
  ·
    rcases fin_succ_cases p with rfl | ⟨k, rfl⟩
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_zero]; exact C.isInMaxIdeal_zero
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)

/-- Compatibility between the corner $\mathrm{GL}_n \hookrightarrow
\mathrm{GL}_{n+1}$ block embedding and the diagonal block embedding: the
conjugate of $\mathrm{diag}(a, M)$ by block embeddings of $A$ and $B$ equals
$\mathrm{diag}(a, AMB)$. -/
theorem blockEmbed_diagBlockEmbed_mul (a : C.kˣ) (A M B : GL (Fin n) C.k) :
    blockEmbedGL C A * diagBlockEmbedGL C a M * blockEmbedGL C B =
    diagBlockEmbedGL C a (A * M * B) := by
  ext1
  simp only [Units.val_mul, diagBlockEmbedGL_val, blockEmbedGL_val,
    blockEmbedMatrix, diagBlockEmbedMatrix]
  rw [← reindexAlgEquiv_mul, fromBlocks_multiply, ← reindexAlgEquiv_mul, fromBlocks_multiply]
  simp

end DiagBlockEmbed

end DVRContext
