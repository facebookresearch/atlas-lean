/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NormalOrderCoeff

def normalOrderCoeff : ℕ → ℕ → ℕ → ℚ
  | i, j, 0 => if i = 0 ∧ j = 0 then 1 else 0
  | i, j, ℓ + 1 =>
    (if j = 0 then 0 else normalOrderCoeff i (j - 1) ℓ) +
    (↑(i + 1) * normalOrderCoeff (i + 1) j ℓ) +
    (if i = 0 then 0 else normalOrderCoeff (i - 1) j ℓ)

@[simp]
theorem normalOrderCoeff_base (i j : ℕ) :
    normalOrderCoeff i j 0 = if i = 0 ∧ j = 0 then 1 else 0 := by
  rfl

theorem normalOrderCoeff_succ (i j ℓ : ℕ) :
    normalOrderCoeff i j (ℓ + 1) =
      (if j = 0 then 0 else normalOrderCoeff i (j - 1) ℓ) +
      (↑(i + 1) * normalOrderCoeff (i + 1) j ℓ) +
      (if i = 0 then 0 else normalOrderCoeff (i - 1) j ℓ) := by
  rfl

def bijCoeffFormula (i j ℓ : ℕ) : ℚ :=
  if i + j ≤ ℓ ∧ (ℓ - i - j) % 2 = 0 then
    (ℓ.factorial : ℚ) /
      (2 ^ ((ℓ - i - j) / 2) * i.factorial * j.factorial * ((ℓ - i - j) / 2).factorial)
  else 0

theorem bijCoeffFormula_eq_zero_of_gt {i j ℓ : ℕ} (h : ℓ < i + j) :
    bijCoeffFormula i j ℓ = 0 := by
  simp [bijCoeffFormula, show ¬(i + j ≤ ℓ) from by omega]

theorem bijCoeffFormula_of_valid {i j ℓ : ℕ} (hij : i + j ≤ ℓ) (heven : (ℓ - i - j) % 2 = 0) :
    bijCoeffFormula i j ℓ = (ℓ.factorial : ℚ) /
      (2 ^ ((ℓ - i - j) / 2) * i.factorial * j.factorial * ((ℓ - i - j) / 2).factorial) := by
  simp [bijCoeffFormula, hij, heven]

theorem bijCoeffFormula_eq_zero {i j ℓ : ℕ} (h : ¬(i + j ≤ ℓ ∧ (ℓ - i - j) % 2 = 0)) :
    bijCoeffFormula i j ℓ = 0 := by
  simp [bijCoeffFormula, h]

theorem denom_ne_zero (m i j : ℕ) :
    (2 : ℚ) ^ m * (i.factorial : ℚ) * (j.factorial : ℚ) * (m.factorial : ℚ) ≠ 0 := by
  positivity

theorem factorial_cast_pred {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℚ) = ↑n * ((n - 1).factorial : ℚ) := by
  rw [← Nat.succ_pred_eq_of_pos hn, Nat.factorial_succ]
  push_cast
  ring

theorem pow_two_pred {n : ℕ} (hn : 0 < n) :
    (2 : ℚ) ^ n = 2 * 2 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ k => simp [pow_succ, mul_comm]

theorem bijCoeffFormula_recurrence (i j ℓ : ℕ) :
    bijCoeffFormula i j (ℓ + 1) =
      (if j = 0 then 0 else bijCoeffFormula i (j - 1) ℓ) +
      (↑(i + 1) * bijCoeffFormula (i + 1) j ℓ) +
      (if i = 0 then 0 else bijCoeffFormula (i - 1) j ℓ) := by

  by_cases hvalid : i + j ≤ ℓ + 1 ∧ (ℓ + 1 - i - j) % 2 = 0
  swap
  · rw [bijCoeffFormula_eq_zero hvalid]
    push_neg at hvalid
    have hT1 : (if j = 0 then (0 : ℚ) else bijCoeffFormula i (j - 1) ℓ) = 0 := by
      split_ifs with hj
      · rfl
      · exact bijCoeffFormula_eq_zero fun ⟨h1, h2⟩ => hvalid (by omega) (by omega)
    have hT2 : ↑(i + 1) * bijCoeffFormula (i + 1) j ℓ = 0 := by
      rw [bijCoeffFormula_eq_zero fun ⟨h1, h2⟩ => hvalid (by omega) (by omega), mul_zero]
    have hT3 : (if i = 0 then (0 : ℚ) else bijCoeffFormula (i - 1) j ℓ) = 0 := by
      split_ifs with hi
      · rfl
      · exact bijCoeffFormula_eq_zero fun ⟨h1, h2⟩ => hvalid (by omega) (by omega)
    rw [hT1, hT2, hT3]
    ring

  obtain ⟨hle, heven⟩ := hvalid
  set m := (ℓ + 1 - i - j) / 2 with hm_def
  by_cases hm0 : m = 0
  ·
    have hij : i + j = ℓ + 1 := by omega

    rw [bijCoeffFormula_of_valid (by omega) (by omega)]
    conv_lhs => rw [show (ℓ + 1 - i - j) / 2 = 0 from by omega]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul]

    have hT2_zero : bijCoeffFormula (i + 1) j ℓ = 0 := bijCoeffFormula_eq_zero_of_gt (by omega)
    rw [hT2_zero, mul_zero, add_zero]

    by_cases hj : j = 0
    · subst hj
      simp only [ite_true]
      by_cases hi : i = 0
      · subst hi; omega
      · simp only [hi, ite_false]
        have hi_eq : i = ℓ + 1 := by omega
        rw [bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs => rw [show (ℓ - (i - 1) - 0) / 2 = 0 from by omega]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul]
        subst hi_eq
        rw [Nat.factorial_succ ℓ]
        push_cast
        field_simp
        ring
    · simp only [hj, ite_false]
      by_cases hi : i = 0
      · subst hi
        simp only [ite_true]
        have hj_eq : j = ℓ + 1 := by omega
        rw [bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs => rw [show (ℓ - 0 - (j - 1)) / 2 = 0 from by omega]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul]
        subst hj_eq
        rw [Nat.factorial_succ ℓ]
        push_cast
        field_simp
        ring
      ·
        simp only [hi, ite_false]
        rw [bijCoeffFormula_of_valid (by omega) (by omega),
            bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs =>
          rw [show (ℓ - i - (j - 1)) / 2 = 0 from by omega,
              show (ℓ - (i - 1) - j) / 2 = 0 from by omega]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul]
        have hdi : (i.factorial : ℚ) ≠ 0 := by positivity
        have hdj : (j.factorial : ℚ) ≠ 0 := by positivity
        have hdj1 : ((j - 1).factorial : ℚ) ≠ 0 := by positivity
        have hdi1 : ((i - 1).factorial : ℚ) ≠ 0 := by positivity
        field_simp
        rw [Nat.factorial_succ ℓ]
        push_cast
        rw [factorial_cast_pred (show 0 < j by omega),
            factorial_cast_pred (show 0 < i by omega)]
        have hcst : (↑ℓ + 1 : ℚ) = ↑i + ↑j := by
          exact_mod_cast hij.symm
        rw [hcst]
        ring
  ·
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0

    rw [bijCoeffFormula_of_valid (by omega) (by omega)]
    rw [show (ℓ + 1 - i - j) / 2 = m from hm_def.symm]

    have hkey : (ℓ - (i + 1) - j) / 2 = m - 1 := by omega
    have hT2_rw : bijCoeffFormula (i + 1) j ℓ = (ℓ.factorial : ℚ) /
        (2 ^ (m - 1) * (i + 1).factorial * j.factorial * (m - 1).factorial) := by
      rw [bijCoeffFormula_of_valid (by omega) (by omega), hkey]
    rw [hT2_rw]

    by_cases hj : j = 0
    · subst hj
      simp only [ite_true, Nat.add_zero] at *
      by_cases hi : i = 0
      · subst hi
        simp only [ite_true, Nat.zero_add] at *
        have hd1 := denom_ne_zero m 0 0
        have hd2 := denom_ne_zero (m - 1) 1 0
        field_simp
        rw [Nat.factorial_succ ℓ]
        push_cast
        have hrel : (↑ℓ + 1 : ℚ) = 2 * ↑m := by
          exact_mod_cast (show ℓ + 1 = 2 * m from by omega)
        rw [factorial_cast_pred hm_pos, pow_two_pred hm_pos, hrel]
        ring
      · simp only [hi, ite_false]
        rw [bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs => rw [show (ℓ - (i - 1) - 0) / 2 = m from by omega]
        have hd1 := denom_ne_zero m i 0
        have hd2 := denom_ne_zero (m - 1) (i + 1) 0
        have hd3 := denom_ne_zero m (i - 1) 0
        field_simp
        rw [Nat.factorial_succ ℓ, Nat.factorial_succ i]
        push_cast
        have hrel : (↑ℓ + 1 : ℚ) = ↑i + 2 * ↑m := by
          exact_mod_cast (show ℓ + 1 = i + 2 * m from by omega)
        rw [factorial_cast_pred (show 0 < i by omega),
            factorial_cast_pred hm_pos, pow_two_pred hm_pos, hrel]
        ring
    · simp only [hj, ite_false]
      by_cases hi : i = 0
      · subst hi
        simp only [ite_true, Nat.zero_add] at *
        rw [bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs => rw [show (ℓ - 0 - (j - 1)) / 2 = m from by omega]
        have hd1 := denom_ne_zero m 0 j
        have hd2 := denom_ne_zero m 0 (j - 1)
        have hd3 := denom_ne_zero (m - 1) 1 j
        field_simp
        rw [Nat.factorial_succ ℓ]
        push_cast
        have hrel : (↑ℓ + 1 : ℚ) = ↑j + 2 * ↑m := by
          exact_mod_cast (show ℓ + 1 = j + 2 * m from by omega)
        rw [factorial_cast_pred (show 0 < j by omega),
            factorial_cast_pred hm_pos, pow_two_pred hm_pos, hrel]
        ring
      ·
        simp only [hi, ite_false]
        rw [bijCoeffFormula_of_valid (by omega) (by omega),
            bijCoeffFormula_of_valid (by omega) (by omega)]
        conv_rhs =>
          rw [show (ℓ - i - (j - 1)) / 2 = m from by omega,
              show (ℓ - (i - 1) - j) / 2 = m from by omega]
        have hd1 := denom_ne_zero m i j
        have hd2 := denom_ne_zero m i (j - 1)
        have hd3 := denom_ne_zero (m - 1) (i + 1) j
        have hd4 := denom_ne_zero m (i - 1) j
        field_simp
        rw [Nat.factorial_succ ℓ, Nat.factorial_succ i]
        push_cast
        have hrel : (↑ℓ + 1 : ℚ) = ↑i + ↑j + 2 * ↑m := by
          exact_mod_cast (show ℓ + 1 = i + j + 2 * m from by omega)
        rw [factorial_cast_pred (show 0 < j by omega),
            factorial_cast_pred (show 0 < i by omega),
            factorial_cast_pred hm_pos, pow_two_pred hm_pos, hrel]
        ring

theorem bijCoeffFormula_zero (i j : ℕ) :
    bijCoeffFormula i j 0 = if i = 0 ∧ j = 0 then 1 else 0 := by
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    simp [bijCoeffFormula, Nat.factorial]
  · have h0 : 0 < i + j := by
      by_contra h
      exact hij ⟨by omega, by omega⟩
    rw [if_neg hij]
    exact bijCoeffFormula_eq_zero_of_gt h0

theorem normalOrderCoeff_eq_bijCoeffFormula (i j ℓ : ℕ) :
    normalOrderCoeff i j ℓ = bijCoeffFormula i j ℓ := by
  suffices h : ∀ i j, normalOrderCoeff i j ℓ = bijCoeffFormula i j ℓ from h i j
  induction ℓ with
  | zero =>
    intro i j
    rw [normalOrderCoeff_base, bijCoeffFormula_zero]
  | succ ℓ ih =>
    intro i j
    rw [normalOrderCoeff_succ]
    simp_rw [ih]
    exact (bijCoeffFormula_recurrence i j ℓ).symm

theorem normalOrderCoeff_eq_zero_of_gt {i j ℓ : ℕ} (h : ℓ < i + j) :
    normalOrderCoeff i j ℓ = 0 := by
  rw [normalOrderCoeff_eq_bijCoeffFormula, bijCoeffFormula_eq_zero_of_gt h]

theorem normalOrderCoeff_of_valid {i j ℓ : ℕ} (hij : i + j ≤ ℓ) (heven : (ℓ - i - j) % 2 = 0) :
    normalOrderCoeff i j ℓ = (ℓ.factorial : ℚ) /
      (2 ^ ((ℓ - i - j) / 2) * i.factorial * j.factorial * ((ℓ - i - j) / 2).factorial) := by
  rw [normalOrderCoeff_eq_bijCoeffFormula, bijCoeffFormula_of_valid hij heven]

abbrev bijCoeff := normalOrderCoeff

theorem bijCoeff_of_valid {i j ℓ : ℕ} (hij : i + j ≤ ℓ) (heven : (ℓ - i - j) % 2 = 0) :
    bijCoeff i j ℓ = (ℓ.factorial : ℚ) /
      (2 ^ ((ℓ - i - j) / 2) * i.factorial * j.factorial * ((ℓ - i - j) / 2).factorial) :=
  normalOrderCoeff_of_valid hij heven

theorem bijCoeff_eq_zero_of_gt {i j ℓ : ℕ} (h : ℓ < i + j) :
    bijCoeff i j ℓ = 0 :=
  normalOrderCoeff_eq_zero_of_gt h

theorem comm_D_U_pow_succ {R : Type*} [Ring R] (D U : R) (hDU : D * U - U * D = 1) :
    ∀ n : ℕ, D * U ^ (n + 1) = U ^ (n + 1) * D + ((n : R) + 1) * U ^ n := by
  have hDU' : D * U = U * D + 1 := by
    rw [sub_eq_iff_eq_add] at hDU
    rw [hDU, add_comm]
  intro n
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, Nat.cast_zero, zero_add, mul_one]
    exact hDU'
  | succ k ih =>
    rw [pow_succ U (k + 1), ← mul_assoc D, ih, add_mul,
        mul_assoc (U ^ (k + 1)) D U, mul_assoc (↑k + 1 : R) (U ^ k) U]
    conv_lhs => rw [hDU']
    rw [mul_add (U ^ (k + 1)) (U * D) 1, mul_one,
        ← mul_assoc (U ^ (k + 1)) U D, ← pow_succ U (k + 1), ← pow_succ U k]
    have hcoeff : (↑(k + 1) + 1 : R) * U ^ (k + 1)
        = 1 * U ^ (k + 1) + (↑k + 1) * U ^ (k + 1) := by
      rw [Nat.cast_succ, show (↑k + 1 + 1 : R) = 1 + (↑k + 1) from by abel]
      rw [add_mul]
    rw [hcoeff, ← add_assoc, one_mul]

def pairsLE (ℓ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (ℓ + 1)) ×ˢ (Finset.range (ℓ + 1))).filter fun p => p.1 + p.2 ≤ ℓ

@[simp]
theorem mem_pairsLE {p : ℕ × ℕ} {ℓ : ℕ} :
    p ∈ pairsLE ℓ ↔ p.1 + p.2 ≤ ℓ := by
  simp [pairsLE, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem D_mul_U_pow_D_pow {R : Type*} [Ring R] (D U : R) (hDU : D * U - U * D = 1)
    (i j : ℕ) : D * (U ^ i * D ^ j) = U ^ i * D ^ (j + 1) + (↑i : R) * (U ^ (i - 1) * D ^ j) := by
  cases i with
  | zero =>
    simp only [pow_zero, one_mul, pow_succ' D, Nat.zero_sub, Nat.cast_zero, zero_mul, add_zero]
  | succ k =>
    simp only [Nat.succ_sub_one]
    rw [← mul_assoc, comm_D_U_pow_succ D U hDU k, add_mul,
        mul_assoc (U ^ (k + 1)) D (D ^ j), ← pow_succ' D, mul_assoc]
    push_cast; rfl

end NormalOrderCoeff
noncomputable section

open NormalOrderCoeff Finset

theorem NormalOrderCoeff.normalOrder_expansion
    {R : Type*} [Ring R] [Algebra ℚ R] (D U : R)
    (hDU : D * U - U * D = 1) (ℓ : ℕ) :
    (D + U) ^ ℓ = ∑ p ∈ NormalOrderCoeff.pairsLE ℓ,
      algebraMap ℚ R (NormalOrderCoeff.normalOrderCoeff p.1 p.2 ℓ) * (U ^ p.1 * D ^ p.2) := by
  induction ℓ with
  | zero =>
    have hpairs : pairsLE 0 = {(0, 0)} := by ext ⟨a, b⟩; simp [mem_pairsLE]
    rw [hpairs, Finset.sum_singleton]
    simp [normalOrderCoeff]
  | succ ℓ ih =>

    simp_rw [← Algebra.smul_def] at ih ⊢

    rw [pow_succ', ih, add_mul, Finset.mul_sum, Finset.mul_sum]
    simp_rw [mul_smul_comm]

    simp_rw [D_mul_U_pow_D_pow D U hDU, ← mul_assoc U, ← pow_succ' U]
    simp_rw [smul_add]
    rw [Finset.sum_add_distrib]

    conv_rhs => arg 2; ext p; rw [normalOrderCoeff_succ]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

    congr 1; congr 1
    ·
      conv_rhs =>
        arg 2; ext x
        rw [show (if x.2 = 0 then (0 : ℚ) else normalOrderCoeff x.1 (x.2 - 1) ℓ) • (U ^ x.1 * D ^ x.2)
          = if x.2 ≠ 0 then normalOrderCoeff x.1 (x.2 - 1) ℓ • (U ^ x.1 * D ^ x.2) else 0
          from by split_ifs <;> simp_all]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      apply Finset.sum_nbij' (fun p => (p.1, p.2 + 1)) (fun p => (p.1, p.2 - 1))
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ _; simp
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab; ext <;> simp; omega
      · intro ⟨a, b⟩ _; simp
    ·

      simp_rw [fun x : ℕ × ℕ => show normalOrderCoeff x.1 x.2 ℓ • ((↑x.1 : R) * (U ^ (x.1 - 1) * D ^ x.2))
        = (↑x.1 * normalOrderCoeff x.1 x.2 ℓ) • (U ^ (x.1 - 1) * D ^ x.2) from by
        rw [show (↑x.1 : R) = algebraMap ℚ R (↑x.1 : ℚ) from (map_natCast _ _).symm,
            ← Algebra.smul_def (↑x.1 : ℚ), ← mul_smul, mul_comm]]

      conv_lhs =>
        arg 2; ext x
        rw [show (↑x.1 * normalOrderCoeff x.1 x.2 ℓ) • (U ^ (x.1 - 1) * D ^ x.2) =
          if x.1 ≠ 0 then (↑x.1 * normalOrderCoeff x.1 x.2 ℓ) • (U ^ (x.1 - 1) * D ^ x.2) else 0
          from by split_ifs with h <;> simp_all]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

      have hR : ∑ x ∈ pairsLE (ℓ + 1), (↑(x.1 + 1) * normalOrderCoeff (x.1 + 1) x.2 ℓ) • (U ^ x.1 * D ^ x.2) =
          ∑ x ∈ pairsLE ℓ, (↑(x.1 + 1) * normalOrderCoeff (x.1 + 1) x.2 ℓ) • (U ^ x.1 * D ^ x.2) := by
        symm; apply Finset.sum_subset (fun p hp => by simp at hp ⊢; omega)
        intro x hx hnotin; simp at hx hnotin
        rw [normalOrderCoeff_eq_zero_of_gt (by omega), mul_zero, zero_smul]
      rw [hR]

      have hR2 : ∑ x ∈ pairsLE ℓ, (↑(x.1 + 1) * normalOrderCoeff (x.1 + 1) x.2 ℓ) • (U ^ x.1 * D ^ x.2) =
          ∑ x ∈ (pairsLE ℓ).filter (fun x => x.1 + 1 + x.2 ≤ ℓ),
            (↑(x.1 + 1) * normalOrderCoeff (x.1 + 1) x.2 ℓ) • (U ^ x.1 * D ^ x.2) := by
        symm; apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hnotin
        simp [Finset.mem_filter] at hx hnotin
        rw [normalOrderCoeff_eq_zero_of_gt (by omega), mul_zero, zero_smul]
      rw [hR2]

      symm
      apply Finset.sum_nbij' (fun p => (p.1 + 1, p.2)) (fun p => (p.1 - 1, p.2))
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ _; simp
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab; ext <;> simp; omega
      · intro ⟨a, b⟩ _; simp
    ·
      conv_rhs =>
        arg 2; ext x
        rw [show (if x.1 = 0 then (0 : ℚ) else normalOrderCoeff (x.1 - 1) x.2 ℓ) • (U ^ x.1 * D ^ x.2)
          = if x.1 ≠ 0 then normalOrderCoeff (x.1 - 1) x.2 ℓ • (U ^ x.1 * D ^ x.2) else 0
          from by split_ifs <;> simp_all]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      apply Finset.sum_nbij' (fun p => (p.1 + 1, p.2)) (fun p => (p.1 - 1, p.2))
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab ⊢; omega
      · intro ⟨a, b⟩ _; simp
      · intro ⟨a, b⟩ hab; simp [Finset.mem_filter] at hab; ext <;> simp; omega
      · intro ⟨a, b⟩ _; simp

end
