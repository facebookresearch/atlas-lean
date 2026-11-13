/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace DisjointUnion

open Matrix SimpleGraph Finset

section DisjointUnionGraph

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
variable (G : SimpleGraph V₁) (H : SimpleGraph V₂) [DecidableRel G.Adj] [DecidableRel H.Adj]


instance instDecidableRelSumAdj : DecidableRel (G ⊕g H).Adj := by
  intro a b
  cases a <;> cases b <;> simp [SimpleGraph.sum] <;> infer_instance

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem neighborFinset_sum_inl (v : V₁) :
    (G ⊕g H).neighborFinset (Sum.inl v) =
      (G.neighborFinset v).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext w
  simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.neighborSet,
    Set.mem_setOf_eq, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases w with
    | inl w => exact ⟨w, hadj, rfl⟩
    | inr w => exact absurd hadj (by simp [SimpleGraph.sum])
  · rintro ⟨w, hadj, rfl⟩
    exact hadj

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem neighborFinset_sum_inr (w : V₂) :
    (G ⊕g H).neighborFinset (Sum.inr w) =
      (H.neighborFinset w).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext v
  simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.neighborSet,
    Set.mem_setOf_eq, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases v with
    | inl v => exact absurd hadj (by simp [SimpleGraph.sum])
    | inr v => exact ⟨v, hadj, rfl⟩
  · rintro ⟨v, hadj, rfl⟩
    exact hadj

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem degree_sum_inl (v : V₁) : (G ⊕g H).degree (Sum.inl v) = G.degree v := by
  simp only [SimpleGraph.degree, neighborFinset_sum_inl, Finset.card_map]

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem degree_sum_inr (w : V₂) : (G ⊕g H).degree (Sum.inr w) = H.degree w := by
  simp only [SimpleGraph.degree, neighborFinset_sum_inr, Finset.card_map]

theorem lapMatrix_sum_eq_fromBlocks :
    (G ⊕g H).lapMatrix ℝ =
      Matrix.fromBlocks (G.lapMatrix ℝ) 0 0 (H.lapMatrix ℝ) := by
  ext (i | i) (j | j)
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₁₁, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, Sum.inl.injEq]
    congr 1
    split_ifs with h
    · congr 1; exact_mod_cast degree_sum_inl G H i
    · rfl
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₁₂, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, zero_apply]
    simp [Sum.inl_ne_inr]
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₂₁, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, zero_apply]
    simp [Sum.inr_ne_inl]
  ·
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      fromBlocks_apply₂₂, sub_apply, diagonal_apply, of_apply,
      SimpleGraph.sum, Sum.inr.injEq]
    congr 1
    split_ifs with h
    · congr 1; exact_mod_cast degree_sum_inr G H i
    · rfl

end DisjointUnionGraph

section DisjointUnionSpectrum

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
variable (G : SimpleGraph V₁) (H : SimpleGraph V₂) [DecidableRel G.Adj] [DecidableRel H.Adj]

open Polynomial

theorem charpoly_roots_fromBlocks_zero {R : Type*} [CommRing R] [IsDomain R]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R) :
    (Matrix.fromBlocks A 0 0 B).charpoly.roots = A.charpoly.roots + B.charpoly.roots := by
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  exact Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic A).ne_zero
    (Matrix.charpoly_monic B).ne_zero)

theorem lapMatrix_sum_charpoly_roots :
    ((G ⊕g H).lapMatrix ℝ).charpoly.roots =
      (G.lapMatrix ℝ).charpoly.roots + (H.lapMatrix ℝ).charpoly.roots := by
  rw [lapMatrix_sum_eq_fromBlocks]
  exact charpoly_roots_fromBlocks_zero (G.lapMatrix ℝ) (H.lapMatrix ℝ)

end DisjointUnionSpectrum

end DisjointUnion
