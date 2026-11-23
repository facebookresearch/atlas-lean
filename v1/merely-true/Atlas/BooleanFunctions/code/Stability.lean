/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Hypercontractivity
import Atlas.BooleanFunctions.code.BonamilBeckner

import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 400000

set_option maxHeartbeats 1600000

open Finset BigOperators Real

namespace BooleanFourier

noncomputable def noiseOperator {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun x => ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2)) * f y

theorem noiseOperator_eq_fourier_sum {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) :
    noiseOperator ρ f x = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S * chi S x := by
  exact noiseOp_eq_fourier_expansion ρ f x

noncomputable def noiseStability {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * noiseOperator ρ f x

lemma sum_chi_mul_chi_eq {n : ℕ} (S T : Finset (Fin n)) :
    ∑ x : Fin n → Bool, chi S x * chi T x =
      if S = T then (2 : ℝ) ^ n else 0 := by
  classical
  split_ifs with h
  · subst h
    simp_rw [chi_mul_self]
    simp [Fintype.card_bool, Fintype.card_fin]
  ·
    have hne : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra hall
      push Not at hall
      have heq : S = T := by
        ext j
        constructor
        · intro hj
          exact by_contra (fun hnjT => hnjT ((hall j).1 hj))
        · intro hj
          exact by_contra (fun hnjS => hnjS ((hall j).2 hj))
      exact h heq
    obtain ⟨j, hj_mem⟩ := hne
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    · intro x
      cases hj_mem with
      | inl hjST =>
        have hflip : chi S (flipAt j x) * chi T (flipAt j x) =
            -(chi S x * chi T x) := by
          rw [chi_flipAt S j hjST.1 x]
          have hT : chi T (flipAt j x) = chi T x := by
            simp only [chi, flipAt]
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjST.2) _ _
          rw [hT]; ring
        linarith
      | inr hjTS =>
        have hflip : chi S (flipAt j x) * chi T (flipAt j x) =
            -(chi S x * chi T x) := by
          rw [chi_flipAt T j hjTS.1 x]
          have hS : chi S (flipAt j x) = chi S x := by
            simp only [chi, flipAt]
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjTS.2) _ _
          rw [hS]; ring
        linarith
    · intro x _
      exact flipAt_ne_self j x
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact flipAt_flipAt j x

theorem noiseStability_eq_sum {n : ℕ} (ρ : ℝ)
    (f : (Fin n → Bool) → ℝ) :
    noiseStability ρ f =
      ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2 := by
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  simp only [noiseStability]
  simp_rw [noiseOperator_eq_fourier_sum]

  conv_lhs =>
    arg 2; arg 2; ext x
    rw [fourier_expansion f x]


  simp_rw [Finset.sum_mul, Finset.mul_sum]

  rw [Finset.sum_comm (s := univ (α := Fin n → Bool))]
  simp_rw [Finset.sum_comm (s := univ (α := Fin n → Bool))]

  simp_rw [show ∀ (T S : Finset (Fin n)) (x : Fin n → Bool),
    fourierCoeff f T * chi T x * (ρ ^ S.card * fourierCoeff f S * chi S x) =
    (fourierCoeff f T * ρ ^ S.card * fourierCoeff f S) * (chi T x * chi S x)
    from fun T S x => by ring]
  simp_rw [← Finset.mul_sum]

  simp_rw [sum_chi_mul_chi_eq]

  simp_rw [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]


  rw [show (1 : ℝ) / 2 ^ n * ∑ x : Finset (Fin n),
      fourierCoeff f x * ρ ^ x.card * fourierCoeff f x * 2 ^ n =
      ∑ x : Finset (Fin n), 1 / 2 ^ n *
        (fourierCoeff f x * ρ ^ x.card * fourierCoeff f x * 2 ^ n) from
    Finset.mul_sum ..]
  congr 1; ext S
  field_simp

noncomputable def majority (n : ℕ) (x : Fin n → Bool) : ℝ :=
  let numTrue := (Finset.univ.filter (fun i => x i = true)).card
  if numTrue * 2 > n then 1
  else if numTrue * 2 < n then -1
  else 0


lemma lpNorm_rpow_eq {n : ℕ} (f : BoolFn n) {p : ℝ} (hp : 0 < p) :
    lpNorm p f ^ p = (1 / (2 ^ n : ℝ)) * ∑ x : Fin n → Bool, |f x| ^ p := by
  unfold lpNorm
  rw [← rpow_mul (by positivity : (0 : ℝ) ≤ (1 / 2 ^ n) *
      ∑ x : Fin n → Bool, |f x| ^ p)]
  simp [hp.ne']


lemma degree_le_iff {n : ℕ} (f : BoolFn n) (d : ℕ) :
    degree f ≤ d ↔ ∀ S : Finset (Fin n), S.card > d → fourierCoeff f S = 0 := by
  unfold degree
  constructor
  · intro h S hS
    by_contra hne
    have hS_mem : S ∈ Finset.univ.filter (fun S : Finset (Fin n) => fourierCoeff f S ≠ 0) := by
      simp [hne]
    have := Finset.le_sup hS_mem (f := Finset.card)
    omega
  · intro h
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    by_contra hlt
    push_neg at hlt
    exact hS (h S (by omega))


end BooleanFourier
