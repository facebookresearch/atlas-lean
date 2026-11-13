/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Stability
import Atlas.BooleanFunctions.code.GaussianStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

open Finset BigOperators Real Filter

namespace BooleanFourier

noncomputable def majorityFn (n : ℕ) : (Fin n → Bool) → ℝ := fun x =>
  if 2 * (Finset.univ.filter (fun i => x i = true)).card > n then 1 else -1

theorem majorityFn_compl {n : ℕ} (hn : Odd n) (x : Fin n → Bool) :
    majorityFn n (fun i => !(x i)) = -(majorityFn n x) := by
  classical
  simp only [majorityFn]
  set k := (univ.filter (fun i : Fin n => x i = true)).card
  have hk_le : k ≤ n := (Finset.card_filter_le _ _).trans (by simp [Finset.card_univ, Fintype.card_fin])
  have hcard : (univ.filter (fun i : Fin n => !(x i) = true)).card = n - k := by
    have heq : (univ.filter (fun i : Fin n => !(x i) = true)).card =
        (univ.filter (fun i : Fin n => x i = false)).card := by
      congr 1; ext i; simp
    rw [heq]
    have hcomp : (univ.filter (fun i : Fin n => x i = false)).card +
        (univ.filter (fun i : Fin n => x i = true)).card =
        (univ : Finset (Fin n)).card := by
      rw [← Finset.card_union_of_disjoint (by
        apply Finset.disjoint_filter.mpr
        intro i _ h1 h2; cases (x i) <;> simp_all)]
      congr 1
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases (x i) <;> simp
    simp [Finset.card_univ, Fintype.card_fin] at hcomp
    omega
  have hsimp : (univ.filter (fun i : Fin n => (fun i => !(x i)) i = true)).card = n - k := by
    convert hcard using 2; ext i; simp
  conv_lhs => rw [hsimp]
  obtain ⟨m, hm⟩ := hn
  split_ifs with h1 h2 <;> try ring <;> omega

theorem chi_compl {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S (fun i => !(x i)) = (-1) ^ S.card * chi S x := by
  simp only [chi]
  rw [show ∏ i ∈ S, boolToReal ((fun i => !(x i)) i) = ∏ i ∈ S, boolToReal (!(x i)) from rfl]
  rw [show ∏ i ∈ S, boolToReal (!(x i)) = ∏ i ∈ S, ((-1) * boolToReal (x i)) from by
    congr 1; ext i; cases (x i) <;> simp [boolToReal]]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem fourierCoeff_majorityFn_even_eq_zero {n : ℕ} (hn : Odd n)
    (S : Finset (Fin n)) (hS : Even S.card) :
    fourierCoeff (majorityFn n) S = 0 := by
  classical
  simp only [fourierCoeff]
  suffices h : ∑ x : Fin n → Bool, majorityFn n x * chi S x = 0 by
    rw [h, mul_zero]
  apply Finset.sum_involution (fun x _ => fun i => !(x i))
  · intro x _
    rw [majorityFn_compl hn x, chi_compl S x, hS.neg_one_pow, one_mul]; ring
  · intro x _ hne
    intro heq
    have h0 : ∀ i, x i = !(x i) := fun i => congr_fun heq.symm i
    exact absurd (h0 ⟨0, by obtain ⟨m, hm⟩ := hn; omega⟩) (by cases (x ⟨0, _⟩) <;> simp)
  · intro x _; exact Finset.mem_univ _
  · intro x _; funext i; simp

end BooleanFourier

noncomputable def BooleanFourier.signFn : ℝ → ℝ := fun x => if x ≥ 0 then 1 else -1

noncomputable def BooleanFourier.gaussianSignCorrelation (ρ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, BooleanFourier.signFn p.1 * BooleanFourier.signFn p.2
    ∂(GaussianStability.rhoCorrelatedGaussian ρ)





namespace BooleanFourier


end BooleanFourier
