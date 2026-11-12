/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BooleanAnalysis

structure WeightedRegularGraph (V : Type*) [Fintype V] [DecidableEq V] where
  weight : V → V → ℝ
  degree : ℝ
  weight_nonneg : ∀ x y, 0 ≤ weight x y
  degree_pos : 0 < degree
  regular : ∀ x, ∑ y : V, weight x y = degree

noncomputable def WeightedRegularGraph.edgeExpansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedRegularGraph V) (S : Finset V) : ℝ :=
  if S = ∅ then 0
  else
    (∑ x ∈ S, ∑ y ∈ Finset.univ.filter (fun v => v ∉ S), G.weight x y) /
      (G.degree * S.card)

theorem WeightedRegularGraph.edgeExpansion_empty {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedRegularGraph V) :
    G.edgeExpansion ∅ = 0 := by
  simp [WeightedRegularGraph.edgeExpansion]

theorem WeightedRegularGraph.edgeExpansion_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedRegularGraph V) (S : Finset V) :
    0 ≤ G.edgeExpansion S := by
  unfold WeightedRegularGraph.edgeExpansion
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      apply Finset.sum_nonneg
      intro y _
      exact G.weight_nonneg x y
    · apply mul_nonneg
      · exact le_of_lt G.degree_pos
      · exact Nat.cast_nonneg _

def flip (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp]
theorem flip_apply_same (x : Fin n → Bool) (i : Fin n) :
    flip x i i = !x i := by
  simp [flip]

@[simp]
theorem flip_apply_ne (x : Fin n → Bool) (i j : Fin n) (h : j ≠ i) :
    flip x i j = x j := by
  simp [flip, Function.update_of_ne h]

theorem flip_injective (x : Fin n → Bool) : Function.Injective (flip x) := by
  intro i j hij
  by_contra h_ne
  have hi : flip x i i = flip x j i := congr_fun hij i
  rw [flip_apply_same, flip_apply_ne x j i h_ne] at hi
  simp at hi

noncomputable def edgeExpansion (n : ℕ) (A : Finset (Fin n → Bool)) : ℝ :=
  if n = 0 ∨ A = ∅ then 0
  else
    ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      p.1 ∈ A ∧ flip p.1 p.2 ∉ A)).card : ℝ) / (n * A.card : ℝ)

theorem edgeExpansion_nonneg (n : ℕ) (A : Finset (Fin n → Bool)) :
    0 ≤ edgeExpansion n A := by
  unfold edgeExpansion
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _

@[simp]
theorem edgeExpansion_empty (n : ℕ) :
    edgeExpansion n (∅ : Finset (Fin n → Bool)) = 0 := by
  simp [edgeExpansion]

noncomputable def edgeBoundaryMeasure (n : ℕ) (A : Finset (Fin n → Bool)) : ℝ :=
  if n = 0 then 0
  else
    ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ)

theorem edgeBoundaryMeasure_def {n : ℕ} (hn : n ≠ 0) (A : Finset (Fin n → Bool)) :
    edgeBoundaryMeasure n A =
      ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
        (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ) := by
  simp [edgeBoundaryMeasure, hn]

end BooleanAnalysis
