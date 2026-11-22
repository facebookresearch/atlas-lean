/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
import Atlas.AnAlgorithmistsToolkit.code.Cheeger
import Atlas.AnAlgorithmistsToolkit.code.Expanders
import Atlas.AnAlgorithmistsToolkit.code.HallTheorem
import Atlas.AnAlgorithmistsToolkit.code.LovaszSimonovits
import Atlas.AnAlgorithmistsToolkit.code.CanonicalPaths
import Mathlib.Analysis.Matrix.Spectrum

namespace RandomWalks

open Matrix SimpleGraph Module.End Finset

section StationaryDist

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def stationaryDist (v : V) : ℝ :=
  (G.degree v : ℝ) / (∑ u : V, (G.degree u : ℝ))

theorem stationaryDist_sum_eq_one
    (hpos : (0 : ℝ) < ∑ u : V, (G.degree u : ℝ)) :
    ∑ v : V, stationaryDist G v = 1 := by
  simp only [stationaryDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

end StationaryDist

section WalkMatrix

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def walkMatrix : Matrix V V ℝ :=
  fun i j => (G.adjMatrix ℝ i j) / (G.degree j : ℝ)

noncomputable def stationaryVec : V → ℝ :=
  fun v => (G.degree v : ℝ) / (∑ u : V, (G.degree u : ℝ))

lemma adjMatrix_row_sum (k : V) :
    ∑ i : V, G.adjMatrix ℝ k i = (G.degree k : ℝ) := by
  rw [G.degree_eq_sum_if_adj k]
  simp only [adjMatrix_apply]

lemma degree_pos_of_adj {k x : V} (h : G.Adj k x) : 0 < G.degree x :=
  Finset.card_pos.mpr ⟨k, by rwa [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]⟩

lemma walkMatrix_stationaryVec_term (k x : V) (S : ℝ) :
    G.adjMatrix ℝ k x / (G.degree x : ℝ) * ((G.degree x : ℝ) / S) =
    G.adjMatrix ℝ k x / S := by
  simp only [adjMatrix_apply]
  split_ifs with h
  · have hd : (G.degree x : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (degree_pos_of_adj G h)
    rw [one_div]
    field_simp
  · simp

theorem walkMatrix_mulVec_stationaryVec :
    (walkMatrix G).mulVec (stationaryVec G) = stationaryVec G := by
  ext k
  simp only [mulVec, dotProduct, walkMatrix, stationaryVec]
  simp_rw [walkMatrix_stationaryVec_term G k _ _]
  rw [← Finset.sum_div, adjMatrix_row_sum]

end WalkMatrix

section RegularGraph

variable {V : Type*} [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

variable [Fintype V]

end RegularGraph

section ConjugationEigenvalues

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem eigenspace_conj_eq (e : M ≃ₗ[R] M) (f : Module.End R M) (μ : R) :
    eigenspace (e.conj f) μ = Submodule.map (e : M →ₗ[R] M) (eigenspace f μ) := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · intro h
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply_apply] at h
    rw [map_smul, e.apply_symm_apply]
    exact h
  · rintro ⟨y, hy, rfl⟩
    show (e.conj f) (e y) = μ • (e y)
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply, hy, map_smul]

theorem hasEigenvalue_conj_iff (e : M ≃ₗ[R] M) (f : Module.End R M) (μ : R) :
    HasEigenvalue (e.conj f) μ ↔ HasEigenvalue f μ := by
  simp only [hasEigenvalue_iff, eigenspace_conj_eq]
  constructor
  · intro h heq
    rw [heq, Submodule.map_bot] at h
    exact h rfl
  · intro h
    rw [Submodule.ne_bot_iff] at h ⊢
    obtain ⟨x, hx, hx_ne⟩ := h
    exact ⟨e x, Submodule.mem_map.mpr ⟨x, hx, rfl⟩,
      fun he => hx_ne (e.injective (by simpa using he))⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def rwMatrixGen : Matrix V V ℝ :=
  G.adjMatrix ℝ * Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹)

noncomputable def normWalkMatrix : Matrix V V ℝ :=
  Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    G.adjMatrix ℝ *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)

theorem normWalkMatrix_eq_conj_rwMatrixGen :
    normWalkMatrix G =
      Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
      rwMatrixGen G *
      Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) := by
  simp only [normWalkMatrix, rwMatrixGen]
  suffices h : Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹) *
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) =
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    rw [Matrix.mul_assoc, h]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext v
  dsimp
  by_cases hd : (G.degree v : ℝ) = 0
  · simp [hd]
  · have hd_pos : (0 : ℝ) < (G.degree v : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hd)
    have hsqrt_ne : Real.sqrt (G.degree v : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hd_pos
    have hsqrt_sq : Real.sqrt (G.degree v : ℝ) * Real.sqrt (G.degree v : ℝ) = (G.degree v : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hd_pos)
    field_simp
    rw [sq, hsqrt_sq]

end ConjugationEigenvalues

section NormLapGen

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end NormLapGen

section LazyWalk

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lazyRwMatrixGen : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 + G.adjMatrix ℝ * Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹))

noncomputable def normLazyWalkMatrix : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 +
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    G.adjMatrix ℝ *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹))

variable (d : ℕ)

noncomputable def lazyRwMatrix : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 + (d : ℝ)⁻¹ • G.adjMatrix ℝ)

end LazyWalk

section LazySymmetry

variable {V : Type*} [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma adjMatrix_isHermitian : (G.adjMatrix ℝ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, SimpleGraph.adjMatrix_apply,
    SimpleGraph.adj_comm]

lemma normLazyWalkMatrix_isHermitian [Fintype V] :
    (normLazyWalkMatrix G).IsHermitian := by
  unfold normLazyWalkMatrix Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  simp only [star_trivial]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.diagonal_conjTranspose, star_trivial, (adjMatrix_isHermitian G).eq]
  rw [mul_assoc]

end LazySymmetry

section L2Dist

noncomputable def l2Norm {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  Real.sqrt (∑ v : V, (f v) ^ 2)

noncomputable def l2Dist {V : Type*} [Fintype V] (p q : V → ℝ) : ℝ :=
  l2Norm (p - q)

end L2Dist



section Convergence

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end Convergence



section MixingBound

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end MixingBound

section NormWalkEigenvalueEquiv

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

lemma sqrtDeg_mul_sqrtDeg_inv
    (hpos : ∀ v : V, 0 < G.degree v) :
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos i))
  · rfl

lemma sqrtDeg_inv_mul_sqrtDeg
    (hpos : ∀ v : V, 0 < G.degree v) :
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos i))
  · rfl

noncomputable def sqrtDegEquiv
    (hpos : ∀ v : V, 0 < G.degree v) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  Matrix.toLin'OfInv (sqrtDeg_inv_mul_sqrtDeg G hpos) (sqrtDeg_mul_sqrtDeg_inv G hpos)

lemma rwMatrixGen_eq_sqrt_mul_normWalkMatrix_mul_sqrt_inv
    (hpos : ∀ v : V, 0 < G.degree v) :
    rwMatrixGen G =
      Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) *
      normWalkMatrix G *
      Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) := by
  have hN := normWalkMatrix_eq_conj_rwMatrixGen G


  have hleft : Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) *
      (Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
      rwMatrixGen G *
      Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ))) *
      Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) =
      rwMatrixGen G := by
    simp only [Matrix.mul_assoc]
    rw [sqrtDeg_mul_sqrtDeg_inv G hpos, Matrix.mul_one]
    rw [← Matrix.mul_assoc, sqrtDeg_mul_sqrtDeg_inv G hpos, Matrix.one_mul]
  rw [← hleft, ← hN]

theorem rwMatrixGen_eq_conj_normWalkMatrix
    (hpos : ∀ v : V, 0 < G.degree v) :
    Matrix.toLin' (rwMatrixGen G) =
      (sqrtDegEquiv G hpos).conj (Matrix.toLin' (normWalkMatrix G)) := by
  have hW := rwMatrixGen_eq_sqrt_mul_normWalkMatrix_mul_sqrt_inv G hpos


  rw [hW]
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

  rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]


  rfl

theorem normWalkMatrix_rwMatrixGen_same_eigenvalues
    (hpos : ∀ v : V, 0 < G.degree v)
    (μ : ℝ) :
    HasEigenvalue (Matrix.toLin' (normWalkMatrix G)) μ ↔
    HasEigenvalue (Matrix.toLin' (rwMatrixGen G)) μ := by
  rw [rwMatrixGen_eq_conj_normWalkMatrix G hpos]
  exact (hasEigenvalue_conj_iff (sqrtDegEquiv G hpos)
    (Matrix.toLin' (normWalkMatrix G)) μ).symm

theorem hasEigenvalue_conj_graph_iff
    (hpos : ∀ v : V, 0 < G.degree v)
    (μ : ℝ) :
    HasEigenvalue (Matrix.toLin' (rwMatrixGen G)) μ ↔
    HasEigenvalue (Matrix.toLin' (normWalkMatrix G)) μ :=
  (normWalkMatrix_rwMatrixGen_same_eigenvalues G hpos μ).symm

end NormWalkEigenvalueEquiv

section ExpanderMatching

theorem expander_matching_contraction_ratio
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : SimpleGraph (L ⊕ R)) [DecidableRel G.Adj]
    {d : ℕ} {α β : ℝ}
    (hbip : G.IsBipartiteOn)
    (hreg : G.IsRegularOfDegree d)
    (hexp : G.IsBipartiteExpander α β)
    (hd : (0 : ℝ) < (d : ℝ))
    (Si : Finset L) (hSi : (Si.card : ℝ) ≤ α * (Fintype.card L : ℝ))
    (hSi_pos : (0 : ℝ) < (Si.card : ℝ))
    (Si1_card : ℝ)
    (hSi1 : Si1_card ≤ (Si.card : ℝ) - ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ)) :
    Si1_card / (Si.card : ℝ) ≤ 2 * (1 - β / (d : ℝ)) := by

  have hlem5 := G.unique_neighbors_lower_bound hbip hreg hexp Si hSi

  have h1 : (2 * β - ↑d) * (Si.card : ℝ) / (d : ℝ) ≤
      ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hd)
  have halg : (Si.card : ℝ) - (2 * β - ↑d) * (Si.card : ℝ) / (d : ℝ) =
      2 * (1 - β / (d : ℝ)) * (Si.card : ℝ) := by field_simp; ring
  have hcore : (Si.card : ℝ) - ((G.uniqueNeighbors Si).card : ℝ) / (d : ℝ) ≤
      2 * (1 - β / (d : ℝ)) * (Si.card : ℝ) := by linarith

  rw [div_le_iff₀ hSi_pos]
  linarith

end ExpanderMatching


end RandomWalks


namespace SimpleGraph

open Finset Real BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



end SimpleGraph
