/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.EdgeExpansion
import Atlas.BooleanFunctions.code.Influence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

namespace BooleanAnalysis

open Finset

def indicator {n : ℕ} (A : Finset (Fin n → Bool)) : (Fin n → Bool) → Bool :=
  fun x => decide (x ∈ A)

theorem indicator_ne_iff {n : ℕ} (A : Finset (Fin n → Bool)) (x y : Fin n → Bool) :
    indicator A x ≠ indicator A y ↔
      (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
  unfold indicator
  constructor
  · intro h
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all
  · intro h
    rcases h with ⟨hx, hny⟩ | ⟨hnx, hy⟩ <;> simp_all

theorem flipCoord_eq_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    BooleanFourier.flipCoord x i = flip x i := by
  ext j
  by_cases h : j = i
  · subst h; simp [BooleanFourier.flipCoord, flip]
  · simp [BooleanFourier.flipCoord, flip, Function.update_of_ne h]

theorem totalInfluence_indicator {n : ℕ} (A : Finset (Fin n → Bool)) :
    BooleanFourier.totalInfluence (indicator A) =
      (∑ i : Fin n, ((Finset.univ.filter (fun x : Fin n → Bool =>
        (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).card : ℝ)) / (2 ^ n : ℝ) := by
  unfold BooleanFourier.totalInfluence BooleanFourier.influence
  simp_rw [flipCoord_eq_flip, indicator_ne_iff]
  rw [← Finset.sum_div]

theorem card_boundary_eq_sum {n : ℕ} (A : Finset (Fin n → Bool)) :
    (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card =
    ∑ i : Fin n, (Finset.univ.filter (fun x : Fin n → Bool =>
      (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).card := by
  classical


  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A)))
    (t := Finset.univ) (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _


  have : (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
      (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).filter
      (fun p => Prod.snd p = i) =
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).map
      ⟨fun x => (x, i), fun a b h => by simpa using congr_arg Prod.fst h⟩ := by
    ext ⟨x, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hP, hj⟩
      subst hj
      exact ⟨x, hP, rfl⟩
    · intro ⟨y, hy, hprod⟩
      cases hprod
      exact ⟨hy, rfl⟩
  rw [this, Finset.card_map]

theorem edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n {n : ℕ} (hn : n ≠ 0)
    (A : Finset (Fin n → Bool)) :
    edgeBoundaryMeasure n A =
      BooleanFourier.totalInfluence (indicator A) / (n : ℝ) := by
  rw [edgeBoundaryMeasure_def hn, totalInfluence_indicator, div_div]
  congr 1
  · have hcard := card_boundary_eq_sum A
    exact_mod_cast hcard
  · ring

end BooleanAnalysis
