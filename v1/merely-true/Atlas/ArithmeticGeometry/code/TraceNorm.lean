/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

variable (K : Type*) (L : Type*) [CommRing K] [CommRing L] [Algebra K L]

/-- The $K$-linear map $L \to L$ given by left multiplication by $\alpha \in L$. -/
noncomputable abbrev mulLeft (α : L) : L →ₗ[K] L :=
  (Algebra.lmul K L) α

/-- The trace map $\mathrm{Tr}_{L/K} : L \to K$ of the algebra $L$ over $K$. -/
noncomputable def traceOfExtension : L →ₗ[K] K :=
  Algebra.trace K L

/-- The norm map $\mathrm{N}_{L/K} : L \to K$ of the algebra $L$ over $K$. -/
noncomputable def normOfExtension : L →* K :=
  Algebra.norm K


/-- The characteristic polynomial of a constant block-diagonal matrix is the characteristic polynomial of the block raised to the number of blocks. -/
lemma Matrix.charpoly_blockDiagonal_const {R : Type*} [CommRing R]
    {n : Type*} [DecidableEq n] [Fintype n]
    {m : Type*} [DecidableEq m] [Fintype m]
    (M : Matrix n n R) :
    (Matrix.blockDiagonal (fun _ : m => M)).charpoly = M.charpoly ^ Fintype.card m := by
  simp only [Matrix.charpoly]
  suffices h : Matrix.charmatrix (Matrix.blockDiagonal (fun _ : m => M)) =
      Matrix.blockDiagonal (fun _ : m => Matrix.charmatrix M) by
    rw [h, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [Matrix.charmatrix, Matrix.blockDiagonal, Matrix.of_apply, Matrix.sub_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
set_option maxHeartbeats 400000 in
open IntermediateField Polynomial Module in
/-- For a finite field extension $L/K$ and $\alpha \in L$ integral over $K$, the characteristic polynomial of multiplication by $\alpha$ is the minimal polynomial of $\alpha$ raised to the power $[L:K]/[K(\alpha):K]$. -/
theorem charpoly_lmul_eq_minpoly_pow
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (α : L) (hα_int : IsIntegral K α) :
    (Algebra.lmul K L α).charpoly = (minpoly K α) ^ (finrank K L / finrank K K⟮α⟯) := by
  let pb := adjoin.powerBasis hα_int
  haveI : FiniteDimensional (↥K⟮α⟯) L := finiteDimensional_right K⟮α⟯
  haveI : FiniteDimensional K (↥K⟮α⟯) := pb.finite
  let bKL := Module.finBasis (↥K⟮α⟯) L
  have hα_eq : α = algebraMap (↥K⟮α⟯) L (AdjoinSimple.gen K α) := by simp

  have h_mat : (LinearMap.toMatrix (pb.basis.smulTower bKL) (pb.basis.smulTower bKL)
      (LinearMap.mulLeft K α)) =
      Matrix.blockDiagonal
        (fun _ => Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)) := by
    rw [Algebra.toMatrix_lmul_eq]
    show Algebra.leftMulMatrix (pb.basis.smulTower bKL) α = _
    calc Algebra.leftMulMatrix (pb.basis.smulTower bKL) α
        = Algebra.leftMulMatrix (pb.basis.smulTower bKL)
            (algebraMap (↥K⟮α⟯) L (AdjoinSimple.gen K α)) := by rw [← hα_eq]
      _ = _ := Algebra.smulTower_leftMulMatrix_algebraMap pb.basis bKL _

  have h_charpoly : (Algebra.lmul K L α).charpoly =
      (Matrix.blockDiagonal (fun _ : Fin (finrank (↥K⟮α⟯) L) =>
        Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α))).charpoly := by
    change (LinearMap.mulLeft K α).charpoly = _
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft K α) (pb.basis.smulTower bKL), h_mat]
  rw [h_charpoly, Matrix.charpoly_blockDiagonal_const, Fintype.card_fin]

  have h_minpoly : (Algebra.leftMulMatrix pb.basis (AdjoinSimple.gen K α)).charpoly =
      minpoly K α := by
    rw [show AdjoinSimple.gen K α = pb.gen from (adjoin.powerBasis_gen hα_int).symm,
        charpoly_leftMulMatrix]
    exact minpoly_gen K α
  rw [h_minpoly]

  congr 1
  exact (Nat.div_eq_of_eq_mul_right finrank_pos
    (finrank_mul_finrank K (↥K⟮α⟯) L).symm).symm
