/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1

open Matrix Real Finset

noncomputable section

/-- The Schatten $q$-norm of a matrix given by SVD `S`:
$\|A\|_{S_q} = \bigl(\sum_j \sigma_j^q\bigr)^{1/q}$. -/
def schattenNorm {d T : ℕ} (S : SVD d T) (q : ℝ) : ℝ :=
  (∑ j : Fin S.r, S.σval j ^ q) ^ (1 / q)

/-- The nuclear norm (Schatten 1-norm) of a matrix given by SVD `S`:
the sum of its singular values. -/
def nuclearNormSVD {d T : ℕ} (S : SVD d T) : ℝ :=
  ∑ j : Fin S.r, S.σval j

/-- The Frobenius (entrywise) inner product of two matrices,
$\langle A, B\rangle_F = \sum_{i,j} A_{ij} B_{ij}$. -/
def frobeniusInnerProduct {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Entrywise commutation of a finite sum of matrices with evaluation at index `(i, j)`. -/
lemma matrix_sum_apply {d T : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin d) (Fin T) ℝ) (i : Fin d) (j : Fin T) :
    (∑ k, f k) i j = ∑ k, f k i j :=
  congr_fun (Finset.sum_apply i Finset.univ f) j |>.trans
    (Finset.sum_apply j Finset.univ (fun k => f k i))

/-- The Frobenius inner product is additive in its first argument across a finite sum. -/
lemma frobeniusInnerProduct_sum {d T : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin d) (Fin T) ℝ) (B : Matrix (Fin d) (Fin T) ℝ) :
    frobeniusInnerProduct (∑ k, f k) B = ∑ k, frobeniusInnerProduct (f k) B := by
  simp only [frobeniusInnerProduct, matrix_sum_apply, Finset.sum_mul]
  simp_rw [show ∀ (a : Fin d), ∑ (b : Fin T), ∑ (c : ι), f c a b * B a b =
    ∑ (c : ι), ∑ (b : Fin T), f c a b * B a b from fun _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- The Frobenius inner product is homogeneous in its first argument under scalar multiplication. -/
lemma frobeniusInnerProduct_smul {d T : ℕ}
    (c : ℝ) (A B : Matrix (Fin d) (Fin T) ℝ) :
    frobeniusInnerProduct (c • A) B = c * frobeniusInnerProduct A B := by
  simp only [frobeniusInnerProduct]
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  simp [smul_eq_mul, mul_assoc]

/-- The Frobenius inner product with a rank-one matrix `u v^⊤` equals the bilinear form
$u^\top B v$. -/
lemma frobeniusInnerProduct_vecMulVec {d T : ℕ}
    (u : Fin d → ℝ) (v : Fin T → ℝ) (B : Matrix (Fin d) (Fin T) ℝ) :
    frobeniusInnerProduct (vecMulVec u v) B = dotProduct u (B.mulVec v) := by
  simp only [frobeniusInnerProduct, vecMulVec, Matrix.of_apply, dotProduct, mulVec]
  congr 1; ext i
  simp only [Finset.mul_sum]
  congr 1; ext j; ring

/-- For unit vectors `u`, `v`, the bilinear form $u^\top B v$ is bounded by the operator norm
of `B`. -/
lemma dotProduct_mulVec_le_opNorm {d T : ℕ}
    (u : Fin d → ℝ) (v : Fin T → ℝ) (B : Matrix (Fin d) (Fin T) ℝ)
    (hu : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ = 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin T))‖ = 1) :
    dotProduct u (B.mulVec v) ≤ matrixOpNorm B := by
  let u_euc : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 u
  let v_euc : EuclideanSpace ℝ (Fin T) := WithLp.toLp 2 v
  have h1 : dotProduct u (B.mulVec v) =
    @inner ℝ _ _ u_euc (toEuclideanLin B v_euc) := by
    simp [inner, dotProduct, toEuclideanLin, toLpLin, mulVec, u_euc, v_euc]
    congr 1; ext i; ring
  rw [h1]
  calc @inner ℝ _ _ u_euc (toEuclideanLin B v_euc)
      ≤ ‖u_euc‖ * ‖toEuclideanLin B v_euc‖ := real_inner_le_norm u_euc _
    _ = ‖u_euc‖ * ‖(toEuclideanLin B).toContinuousLinearMap v_euc‖ := by
        simp [LinearMap.toContinuousLinearMap]
    _ ≤ ‖u_euc‖ * (‖(toEuclideanLin B).toContinuousLinearMap‖ * ‖v_euc‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = matrixOpNorm B := by rw [hu, hv]; simp [matrixOpNorm]

/-- Extend the singular values of `S` (defined on `Fin S.r`) to all of `Fin (min d T)` by
zero, so that comparisons between SVDs of different ranks are easier. -/
def extendedσval {d T : ℕ} (S : SVD d T) (j : Fin (min d T)) : ℝ :=
  if h : j.val < S.r then S.σval ⟨j.val, h⟩ else 0

/-- The extended singular values are nonnegative. -/
lemma extendedσval_nonneg {d T : ℕ} (S : SVD d T) (j : Fin (min d T)) :
    0 ≤ extendedσval S j := by
  simp only [extendedσval]; split_ifs with h
  · exact S.σval_nonneg _
  · exact le_refl _

/-- A finite sum over `Fin n` of a function that vanishes beyond index `r` equals the
restricted sum over `Fin r`. -/
lemma sum_fin_of_zero_tail {r n : ℕ} (hr : r ≤ n) (f : Fin n → ℝ)
    (hf : ∀ j : Fin n, r ≤ j.val → f j = 0) :
    ∑ j : Fin n, f j = ∑ j : Fin r, f ⟨j.val, by omega⟩ := by
  classical
  have key : ∀ j : Fin n, f j = if j.val < r then f j else 0 := by
    intro j
    split_ifs with h
    · rfl
    · exact hf j (by omega)
  conv_lhs =>
    arg 2; ext j; rw [key j]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  symm
  apply Finset.sum_nbij (fun (j : Fin r) => (⟨j.val, by omega⟩ : Fin n))
  · intro j _; simp [j.isLt]
  · intro a b _ _ h; exact Fin.ext (Fin.mk.inj h)
  · intro b hb
    simp at hb
    exact ⟨⟨b.val, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a ha; rfl

/-- The $p$-th power sum of the extended singular values reduces to the corresponding sum
over the original `Fin S.r` singular values. -/
lemma sum_extendedσval_rpow {d T : ℕ} (S : SVD d T) (p : ℝ) (hp : 0 < p) :
    ∑ j : Fin (min d T), (extendedσval S j) ^ p =
    ∑ j : Fin S.r, (S.σval j) ^ p := by
  rw [sum_fin_of_zero_tail S.hr]
  · congr 1; ext j; simp [extendedσval, j.isLt]
  · intro j hj
    simp [extendedσval, show ¬(j.val < S.r) from by omega, hp.ne']

/-- Exponents `p, q ≥ 1` satisfying $1/p + 1/q = 1$ are Hölder conjugates. -/
lemma holderConjugate_of_div_add {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 / p + 1 / q = 1) : p.HolderConjugate q := by
  rw [Real.holderConjugate_iff]
  constructor
  · by_contra h
    push Not at h
    have hpe : p = 1 := le_antisymm h hp
    subst hpe; simp at hpq; linarith
  · rwa [one_div, one_div] at hpq


/-- **Hölder's inequality for Schatten norms (nuclear/operator case).** The Frobenius inner
product satisfies $\langle A, B\rangle_F \le \|A\|_* \cdot \|B\|_{op}$. -/
theorem holder_schatten_nuclear_op {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (S_A : SVD d T) (hA : S_A.IsDecompOf A)
    (hu : ∀ j, ‖(WithLp.toLp 2 (S_A.u j) : EuclideanSpace ℝ (Fin d))‖ = 1)
    (hv : ∀ j, ‖(WithLp.toLp 2 (S_A.v j) : EuclideanSpace ℝ (Fin T))‖ = 1) :
    frobeniusInnerProduct A B ≤ nuclearNormSVD S_A * matrixOpNorm B := by

  rw [hA, SVD.toMatrix]

  rw [frobeniusInnerProduct_sum]
  simp_rw [frobeniusInnerProduct_smul, frobeniusInnerProduct_vecMulVec]

  rw [nuclearNormSVD, Finset.sum_mul]

  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left
    (dotProduct_mulVec_le_opNorm _ _ B (hu k) (hv k))
    (S_A.σval_nonneg k)


end
