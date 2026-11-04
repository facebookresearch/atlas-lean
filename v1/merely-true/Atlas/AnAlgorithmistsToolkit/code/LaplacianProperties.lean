/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Atlas.AnAlgorithmistsToolkit.code.SingleEdgeLaplacian

namespace PSDMatrix

open Matrix

abbrev IsPSD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosSemidef

abbrev IsPD {n : Type*} (M : Matrix n n ℝ) : Prop := M.PosDef

theorem isPSD_iff_eigenvalues_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    IsPSD M ↔ ∀ i, 0 ≤ hM.eigenvalues i := by
  rw [show IsPSD M ↔ M.PosSemidef from Iff.rfl, hM.posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  simp

theorem isPD_iff_eigenvalues_pos {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    IsPD M ↔ ∀ i, 0 < hM.eigenvalues i :=
  hM.posDef_iff_eigenvalues_pos

theorem isPSD_and_isPD_iff_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (IsPSD M ↔ ∀ i, 0 ≤ hM.eigenvalues i) ∧
    (IsPD M ↔ ∀ i, 0 < hM.eigenvalues i) :=
  ⟨isPSD_iff_eigenvalues_nonneg hM, isPD_iff_eigenvalues_pos hM⟩

open scoped MatrixOrder

lemma star_eq_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) : star B = Bᵀ := by
  ext i j; simp [star, Matrix.transpose]

lemma conjTranspose_eq_transpose_real {n m : Type*} [Fintype n] [Fintype m]
    (B : Matrix m n ℝ) : B.conjTranspose = Bᵀ := by
  ext i j; simp [conjTranspose]

theorem isPSD_iff_exists_transpose_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    IsPSD M ↔ ∃ B : Matrix n n ℝ, M = Bᵀ * B := by
  constructor
  ·


    intro hM
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
    exact ⟨B, by rwa [star_eq_transpose] at hB⟩
  ·

    rintro ⟨B, rfl⟩
    rw [← conjTranspose_eq_transpose_real]
    exact posSemidef_conjTranspose_mul_self B

universe u_psd in
theorem isPSD_iff_exists_transpose_mul_self_rect {n : Type u_psd} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    IsPSD M ↔ ∃ (k : Type u_psd) (_ : Fintype k) (B : Matrix k n ℝ), M = Bᵀ * B := by
  constructor
  ·

    intro hM
    obtain ⟨B, hB⟩ := (isPSD_iff_exists_transpose_mul_self M).mp hM
    exact ⟨n, inferInstance, B, hB⟩
  ·

    rintro ⟨k, fk, B, rfl⟩
    rw [← conjTranspose_eq_transpose_real]
    exact posSemidef_conjTranspose_mul_self B

end PSDMatrix

open Matrix SimpleGraph Finset BigOperators

namespace LaplacianProperties

open Matrix SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma eq_of_adj_of_mulVec_eq_zero (x : V → ℝ) (hx : (G.lapMatrix ℝ).mulVec x = 0)
    (i j : V) (hadj : G.Adj i j) : x i = x j := by
  have hdot : x ⬝ᵥ ((G.lapMatrix ℝ).mulVec x) = 0 := by
    rw [hx]; simp [dotProduct]
  have hqf := lapMatrix_toLinearMap₂' ℝ G x
  rw [toLinearMap₂'_apply'] at hqf
  rw [hdot] at hqf
  have hsum_zero : (∑ a : V, ∑ b : V, if G.Adj a b then (x a - x b) ^ 2 else 0) = (0 : ℝ) := by
    linarith
  have hinner_nonneg : ∀ a ∈ Finset.univ,
      (0 : ℝ) ≤ ∑ b : V, if G.Adj a b then (x a - x b) ^ 2 else 0 := by
    intro a _; exact Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
  have hi_zero :=
    ((Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).mp hsum_zero) i (mem_univ i)
  have hterm_nonneg : ∀ b ∈ Finset.univ,
      (0 : ℝ) ≤ if G.Adj i b then (x i - x b) ^ 2 else 0 := by
    intro b _; split_ifs <;> positivity
  have hj :=
    ((Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hi_zero) j (mem_univ j)
  simp only [hadj, ite_true] at hj
  nlinarith [sq_nonneg (x i - x j)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma eq_const_of_adj_eq (hconn : G.Connected) (x : V → ℝ)
    (hadj_eq : ∀ i j : V, G.Adj i j → x i = x j)
    (v₀ w : V) : x w = x v₀ := by
  have hreach := hconn.preconnected v₀ w
  rw [reachable_eq_reflTransGen] at hreach
  induction hreach with
  | refl => rfl
  | tail _ hadj ih => exact (hadj_eq _ _ hadj).symm ▸ ih

theorem ker_lapMatrix_eq_span_ones (hconn : G.Connected) :
    LinearMap.ker (G.lapMatrix ℝ).mulVecLin = Submodule.span ℝ {fun _ : V => (1 : ℝ)} := by
  ext x
  rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  ·
    intro hx
    obtain ⟨v₀⟩ := hconn.nonempty
    have hadj_eq := eq_of_adj_of_mulVec_eq_zero G x hx
    have hconst := eq_const_of_adj_eq G hconn x hadj_eq v₀
    exact ⟨x v₀, by
      ext w
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact (hconst w).symm⟩
  ·
    rintro ⟨c, rfl⟩
    rw [mulVec_smul, lapMatrix_mulVec_const_eq_zero]
    exact smul_zero c

open Matrix SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

section EdgeUnion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

set_option linter.unusedSectionVars false in
theorem adjMatrix_sup_of_disjoint (hd : Disjoint G H) :
    (G ⊔ H).adjMatrix ℝ = G.adjMatrix ℝ + H.adjMatrix ℝ := by
  classical
  ext i j
  simp only [SimpleGraph.adjMatrix_apply, Matrix.add_apply, sup_adj]
  have hne : ¬(G.Adj i j ∧ H.Adj i j) := by
    intro ⟨hG, hH⟩
    have hinf : G ⊓ H = ⊥ := disjoint_iff.mp hd
    have := (inf_adj G H i j).mpr ⟨hG, hH⟩
    rw [hinf] at this
    exact (bot_adj i j).mp this
  by_cases hG : G.Adj i j <;> by_cases hH : H.Adj i j <;> simp_all

theorem degree_sup_of_disjoint (hd : Disjoint G H) (v : V) :
    (G ⊔ H).degree v = G.degree v + H.degree v := by
  classical
  have hinf : G ⊓ H = ⊥ := disjoint_iff.mp hd
  simp only [SimpleGraph.degree]
  have hdisjoint : Disjoint (G.neighborFinset v) (H.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [SimpleGraph.mem_neighborFinset] at hw1 hw2
    have := (inf_adj G H v w).mpr ⟨hw1, hw2⟩
    rw [hinf] at this
    exact (bot_adj v w).mp this
  have heq : (G ⊔ H).neighborFinset v = G.neighborFinset v ∪ H.neighborFinset v := by
    ext w
    simp [SimpleGraph.mem_neighborFinset, sup_adj]
  rw [heq]
  exact Finset.card_union_of_disjoint hdisjoint

theorem degMatrix_sup_of_disjoint (hd : Disjoint G H) :
    (G ⊔ H).degMatrix ℝ = G.degMatrix ℝ + H.degMatrix ℝ := by
  classical
  ext i j
  simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply, Matrix.add_apply]
  split_ifs with h
  · subst h
    push_cast [degree_sup_of_disjoint G H hd i]
    ring
  · simp

theorem lapMatrix_sup_of_disjoint (hd : Disjoint G H) :
    (G ⊔ H).lapMatrix ℝ = G.lapMatrix ℝ + H.lapMatrix ℝ := by
  classical
  simp only [SimpleGraph.lapMatrix]
  rw [degMatrix_sup_of_disjoint G H hd, adjMatrix_sup_of_disjoint G H hd]
  abel

end EdgeUnion

section IsolatedVertices

omit [DecidableEq V] in
lemma not_adj_of_degree_zero {v : V} (hdeg : G.degree v = 0) (j : V) : ¬G.Adj v j := by
  intro hadj
  have hmem := (G.mem_neighborFinset v j).mpr hadj
  rw [SimpleGraph.degree, Finset.card_eq_zero] at hdeg
  simp [hdeg] at hmem

theorem lapMatrix_row_eq_zero_of_degree_zero {v : V} (hdeg : G.degree v = 0) (j : V) :
    G.lapMatrix ℝ v j = 0 := by
  by_cases hvj : v = j
  · subst hvj
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal,
      SimpleGraph.adjMatrix_apply, hdeg]
  · have hnadj : ¬G.Adj v j := not_adj_of_degree_zero G hdeg j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal, hvj,
      SimpleGraph.adjMatrix_apply, hnadj]

theorem lapMatrix_col_eq_zero_of_degree_zero {v : V} (hdeg : G.degree v = 0) (j : V) :
    G.lapMatrix ℝ j v = 0 := by
  have hsymm : (G.lapMatrix ℝ).IsSymm := SimpleGraph.isSymm_lapMatrix ℝ G
  rw [hsymm.apply v j]
  exact lapMatrix_row_eq_zero_of_degree_zero G hdeg j

theorem lapMatrix_eq_zero_of_degree_zero {v : V} (hdeg : G.degree v = 0) (j : V) :
    G.lapMatrix ℝ v j = 0 ∧ G.lapMatrix ℝ j v = 0 :=
  ⟨lapMatrix_row_eq_zero_of_degree_zero G hdeg j, lapMatrix_col_eq_zero_of_degree_zero G hdeg j⟩

end IsolatedVertices

section NullspaceDimension

theorem dim_ker_lapMatrix_eq_card_connectedComponent :
    Module.finrank ℝ (LinearMap.ker (G.lapMatrix ℝ).mulVecLin) =
      Fintype.card G.ConnectedComponent := by
  have h : (G.lapMatrix ℝ).mulVecLin = (G.lapMatrix ℝ).toLin' := by
    ext x; simp [Matrix.toLin'_apply']
  rw [h]
  exact G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix.symm

end NullspaceDimension

open Matrix SimpleGraph Finset BigOperators Polynomial

open Matrix SimpleGraph Finset BigOperators

open Matrix SimpleGraph Finset BigOperators

end LaplacianProperties
