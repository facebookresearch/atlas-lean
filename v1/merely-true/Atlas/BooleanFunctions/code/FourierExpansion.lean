/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Finset BigOperators

namespace BooleanFourier

noncomputable def boolToReal (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp]
lemma boolToReal_true : boolToReal true = 1 := by
  simp [boolToReal]

@[simp]
lemma boolToReal_false : boolToReal false = -1 := by
  simp [boolToReal]

lemma boolToReal_sq (b : Bool) : boolToReal b ^ 2 = 1 := by
  cases b <;> simp [boolToReal]

lemma boolToReal_ne_zero (b : Bool) : boolToReal b ≠ 0 := by
  cases b <;> simp [boolToReal]

lemma boolToReal_mul_self (b : Bool) : boolToReal b * boolToReal b = 1 := by
  cases b <;> simp [boolToReal]

lemma boolToReal_not (b : Bool) : boolToReal (!b) = -boolToReal b := by
  cases b <;> simp [boolToReal]

lemma one_add_boolToReal_mul_boolToReal (a b : Bool) :
    1 + boolToReal a * boolToReal b = if a = b then 2 else 0 := by
  cases a <;> cases b <;> simp [boolToReal] <;> norm_num

noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, boolToReal (x i)

@[simp]
lemma chi_empty {n : ℕ} (x : Fin n → Bool) : chi ∅ x = 1 := by
  simp [chi]

lemma chi_sq {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x ^ 2 = 1 := by
  simp only [chi, ← Finset.prod_pow]
  simp [boolToReal_sq]

lemma chi_mul_self {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x * chi S x = 1 := by
  have h := chi_sq S x
  linarith [sq_abs (chi S x), h, sq_nonneg (chi S x)]

lemma chi_ne_zero {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x ≠ 0 := by
  simp only [chi]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => boolToReal_ne_zero (x i))

noncomputable def fourierCoeff {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x

def flipAt {n : ℕ} (j : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x j (!x j)

lemma flipAt_flipAt {n : ℕ} (j : Fin n) (x : Fin n → Bool) :
    flipAt j (flipAt j x) = x := by
  ext i
  simp only [flipAt, Function.update]
  split_ifs with h
  · subst h; simp
  · rfl

lemma flipAt_ne_self {n : ℕ} (j : Fin n) (x : Fin n → Bool) :
    flipAt j x ≠ x := by
  intro h
  have := congr_fun h j
  simp [flipAt, Function.update_self] at this

lemma chi_flipAt {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (x : Fin n → Bool) : chi S (flipAt j x) = -chi S x := by
  simp only [chi, flipAt]
  have hlhs : ∏ i ∈ S, boolToReal (Function.update x j (!x j) i) =
      boolToReal (Function.update x j (!x j) j) *
      ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) :=
    (Finset.mul_prod_erase S _ hj).symm
  have hrhs : ∏ i ∈ S, boolToReal (x i) =
      boolToReal (x j) * ∏ i ∈ S.erase j, boolToReal (x i) :=
    (Finset.mul_prod_erase S _ hj).symm
  rw [hlhs, hrhs]
  have h1 : boolToReal (Function.update x j (!x j) j) = -boolToReal (x j) := by
    simp [Function.update_self, boolToReal_not]
  have h2 : ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) =
      ∏ i ∈ S.erase j, boolToReal (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [h1, h2]
  ring

lemma sum_chi {n : ℕ} (S : Finset (Fin n)) :
    ∑ x : Fin n → Bool, chi S x = if S = ∅ then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · subst h
    simp [chi, Fintype.card_bool]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    · intro x
      have := chi_flipAt S j hj x
      linarith
    · intro x _
      exact flipAt_ne_self j x
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact flipAt_flipAt j x

lemma sum_chi_mul_chi {n : ℕ} (x y : Fin n → Bool) :
    ∑ S : Finset (Fin n), chi S x * chi S y =
      if x = y then (2 : ℝ) ^ n else 0 := by
  classical
  have hprod : ∀ S : Finset (Fin n),
      chi S x * chi S y = ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) := by
    intro S
    simp only [chi, Finset.prod_mul_distrib]
  simp_rw [hprod]
  have hkey : ∑ S : Finset (Fin n),
      ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) =
      ∏ i : Fin n, (1 + boolToReal (x i) * boolToReal (y i)) := by
    conv_lhs =>
      rw [show (∑ S : Finset (Fin n),
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i))) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) from by
          rw [Finset.powerset_univ]]
    rw [← Finset.prod_one_add]
  rw [hkey]
  simp_rw [one_add_boolToReal_mul_boolToReal]
  split_ifs with h
  · subst h
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem fourier_expansion {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    f x = ∑ S : Finset (Fin n), fourierCoeff f S * chi S x := by
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp only [fourierCoeff, one_div]


  have key : ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ *
      (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
      ((2 : ℝ) ^ n)⁻¹ * (f x * (2 : ℝ) ^ n) := by
    have step1 : ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ *
        (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
        ((2 : ℝ) ^ n)⁻¹ * ∑ S : Finset (Fin n),
          (∑ y : Fin n → Bool, f y * chi S y) * chi S x := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [step1]
    congr 1
    have step2 : ∑ S : Finset (Fin n),
        (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
        ∑ S : Finset (Fin n),
          ∑ y : Fin n → Bool, f y * chi S y * chi S x := by
      congr 1; ext S; exact Finset.sum_mul (Finset.univ) _ _
    rw [step2, Finset.sum_comm]
    have step3 : ∑ y : Fin n → Bool,
        ∑ S : Finset (Fin n), f y * chi S y * chi S x =
        ∑ y : Fin n → Bool,
          f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
      congr 1; ext y
      have : ∑ S : Finset (Fin n), f y * chi S y * chi S x =
          f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
        simp_rw [show ∀ S : Finset (Fin n), f y * chi S y * chi S x =
          f y * (chi S y * chi S x) from fun S => by ring]
        rw [← Finset.mul_sum (a := f y) (s := Finset.univ)]
      exact this
    rw [step3]
    simp_rw [sum_chi_mul_chi, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp only [Finset.mem_univ, ite_true]
  rw [key]
  field_simp

noncomputable def levelComponent {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    fourierCoeff f S * chi S x

noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun S : Finset (Fin n) => fourierCoeff f S ≠ 0))
    Finset.card

end BooleanFourier
