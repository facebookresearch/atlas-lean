/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset

namespace Sparsification

variable {n : Type*} {𝕜 : Type*} [RCLike 𝕜]

theorem loewner_order_iff_posSemidef (M N : Matrix n n 𝕜) :
    N ≤ M ↔ (M - N).PosSemidef :=
  Matrix.le_iff

section GraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

def GraphLoewnerLE (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  H.lapMatrix ℝ ≤ G.lapMatrix ℝ

def IsSpectralSparsifier (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (ε : ℝ) : Prop :=
  (G.lapMatrix ℝ - (1 - ε) • G'.lapMatrix ℝ).PosSemidef ∧
  ((1 + ε) • G'.lapMatrix ℝ - G.lapMatrix ℝ).PosSemidef

end GraphOrdering

section WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

structure SymmWeights (V : Type*) where
  w : V → V → ℝ
  symm : ∀ i j, w i j = w j i
  diag_zero : ∀ i, w i i = 0

noncomputable def weightedLapMatrix (W : SymmWeights V) : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ∑ k : V, W.w i k
    else -W.w i j

lemma weightedLap_inner_sum (W : SymmWeights V) (x : V → ℝ) (i : V) :
    ∑ j : V, (if i = j then ∑ k : V, W.w i k else -W.w i j) * x j =
    (∑ k : V, W.w i k) * x i - ∑ j : V, W.w i j * x j := by
  have h1 : ∑ j : V, (if i = j then ∑ k : V, W.w i k else -W.w i j) * x j =
    (∑ k : V, W.w i k) * x i + ∑ j ∈ Finset.univ.erase i, (-W.w i j * x j) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [hij]
  rw [h1]
  have h2 : ∑ j ∈ Finset.univ.erase i, (-W.w i j * x j) =
    -(∑ j ∈ Finset.univ.erase i, W.w i j * x j) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [h2]
  have h3 : ∑ j : V, W.w i j * x j =
    W.w i i * x i + ∑ j ∈ Finset.univ.erase i, W.w i j * x j := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [h3, W.diag_zero, zero_mul, zero_add]
  ring

theorem weightedLap_quadform_eq (W : SymmWeights V) (x : V → ℝ) :
    x ⬝ᵥ (weightedLapMatrix W).mulVec x =
    ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
  simp only [dotProduct, mulVec, weightedLapMatrix, Matrix.of_apply]
  congr 1; ext i
  trans (x i * ((∑ k : V, W.w i k) * x i - ∑ j : V, W.w i j * x j))
  · congr 1; exact weightedLap_inner_sum W x i
  · rw [mul_sub]
    have h1 : x i * ((∑ k : V, W.w i k) * x i) = ∑ j : V, W.w i j * x i ^ 2 := by
      rw [← Finset.sum_mul]; ring
    have h2 : x i * ∑ j : V, W.w i j * x j = ∑ j : V, W.w i j * x i * x j := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [h1, h2, ← Finset.sum_sub_distrib]
    congr 1; ext j; ring

omit [DecidableEq V] in
lemma sum_swap_quadform (W : SymmWeights V) (x : V → ℝ) :
    ∑ i : V, ∑ j : V, W.w i j * x j * (x j - x i) =
    ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
  calc ∑ i : V, ∑ j : V, W.w i j * x j * (x j - x i)
      = ∑ j : V, ∑ i : V, W.w i j * x j * (x j - x i) := by rw [Finset.sum_comm]
    _ = ∑ j : V, ∑ i : V, W.w j i * x j * (x j - x i) := by
        congr 1; ext j; congr 1; ext i; rw [W.symm]
    _ = ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
        rw [Finset.sum_comm]

omit [DecidableEq V] in
lemma quadform_half_sum (W : SymmWeights V) (x : V → ℝ) :
    ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) =
    (1/2) * ∑ i : V, ∑ j : V, W.w i j * (x i - x j) ^ 2 := by
  have expand : ∀ i j : V, W.w i j * (x i - x j) ^ 2 =
    W.w i j * x i * (x i - x j) + W.w i j * x j * (x j - x i) := by
    intro i j; ring
  simp_rw [expand, Finset.sum_add_distrib]
  linarith [sum_swap_quadform W x]

theorem weightedLapMatrix_posSemidef (W : SymmWeights V) (hw : ∀ i j, 0 ≤ W.w i j) :
    (weightedLapMatrix W).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [weightedLapMatrix, Matrix.of_apply, Matrix.transpose_apply]
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [W.symm]
  · intro x
    simp only [star_trivial]
    rw [weightedLap_quadform_eq, quadform_half_sum]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (hw i j) (sq_nonneg _)

theorem weightedLapMatrix_sub_eq (W₁ W₂ : SymmWeights V) :
    weightedLapMatrix W₁ - weightedLapMatrix W₂ =
    weightedLapMatrix ⟨fun i j => W₁.w i j - W₂.w i j,
      fun i j => by simp [W₁.symm, W₂.symm],
      fun i => by simp [W₁.diag_zero, W₂.diag_zero]⟩ := by
  ext i j
  simp only [weightedLapMatrix, Matrix.of_apply, Matrix.sub_apply]
  split_ifs with h
  · simp [Finset.sum_sub_distrib]
  · ring

theorem claim6_weight_monotone_loewner (W_G W_H : SymmWeights V)
    (hw : ∀ i j, W_H.w i j ≤ W_G.w i j) :
    weightedLapMatrix W_H ≤ weightedLapMatrix W_G := by
  rw [Matrix.le_iff, weightedLapMatrix_sub_eq]
  exact weightedLapMatrix_posSemidef _ (fun i j => by linarith [hw i j])

end WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutValue (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet).filter fun e =>
    e.out.1 ∈ S ∧ e.out.2 ∉ S ∨ e.out.1 ∉ S ∧ e.out.2 ∈ S).card

def IsNontrivialCut (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ

noncomputable def minCutValue (G : SimpleGraph V) : ℕ :=
  if h : ∃ S : Finset V, IsNontrivialCut S then
    (Finset.univ.filter (fun S => IsNontrivialCut S)).image (cutValue G)
      |>.min' (by
        rw [Finset.Nonempty]
        obtain ⟨S, hS⟩ := h
        exact ⟨cutValue G S,
          Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩⟩)
  else 0

noncomputable def nontrivialCutsOfValueAtMost
    (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter fun S => IsNontrivialCut S ∧ cutValue G S ≤ k

end Sparsification

