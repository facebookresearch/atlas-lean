/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace IntegerLongDivision

/-- One step of binary long division by `b`: given the current quotient/remainder pair `qr` and the
next bit `bit` of the dividend, shift the partial quotient/remainder left by one (i.e., multiply by
`2`), add `bit` to the remainder, and conditionally subtract `b` to keep the remainder smaller
than `b`. -/
def longDivStep (b : ℕ) (bit : Bool) (qr : ℕ × ℕ) : ℕ × ℕ :=
  let q' := 2 * qr.1
  let r' := 2 * qr.2 + bit.toNat
  if r' < b then (q', r') else (q' + 1, r' - b)

/-- Recursive driver of binary long division: starting from the most significant bit `m` of `a`,
folds `longDivStep` over `k+1` iterations consuming successive bits from `m` down to `m - k - 1`.
The result is the quotient/remainder pair after processing those bits. -/
def longDivLoop (a b m : ℕ) : ℕ → ℕ × ℕ
  | 0     => longDivStep b (a.testBit m) (0, 0)
  | k + 1 => longDivStep b (a.testBit (m - k - 1)) (longDivLoop a b m k)

/-- Schoolbook binary long division of `a` by `b`, treating `a` as an `(m+1)`-bit number: returns
the quotient/remainder pair after processing all bits from position `m` down to `0`. -/
def longDiv (a b m : ℕ) : ℕ × ℕ := longDivLoop a b m m

/-- The `k`-th bit of `n` (as a `Nat`) equals `n / 2 ^ k mod 2`. -/
lemma testBit_toNat_eq_mod_two (n k : ℕ) : (n.testBit k).toNat = n / 2 ^ k % 2 := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have h : n / 2 ^ k % 2 = 0 ∨ n / 2 ^ k % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

/-- Bit-shift identity for integer division: `a / 2^k = 2 * (a / 2^(k+1)) + bit_k(a)`. This is the
key relation that makes binary long division advance by exactly one bit per step. -/
lemma div_pow_two_step (a k : ℕ) :
    a / 2 ^ k = 2 * (a / 2 ^ (k + 1)) + (a.testBit k).toNat := by
  rw [testBit_toNat_eq_mod_two]
  have : a / 2 ^ (k + 1) = a / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [this]; omega

/-- Single-step invariant for `longDivStep`: if the incoming remainder `r` is `< b`, then the
output pair `(q', r')` satisfies `q' * b + r' = 2 * (q * b + r) + bit` and `r' < b`. -/
lemma longDivStep_invariant (b : ℕ) (bit : Bool) (q r : ℕ) (hr : r < b) :
    let res := longDivStep b bit (q, r)
    res.1 * b + res.2 = 2 * (q * b + r) + bit.toNat ∧ res.2 < b := by
  unfold longDivStep; simp only
  split_ifs with h
  · exact ⟨by ring, h⟩
  · push Not at h
    constructor
    · nlinarith [Nat.sub_add_cancel h]
    · have : bit.toNat ≤ 1 := by cases bit <;> simp
      omega

/-- Loop invariant for `longDivLoop`: after processing `k+1` bits, the result pair `(q, r)` satisfies
`q * b + r = a / 2^(m - k)` and `r < b`. This expresses that the loop computes the correct partial
quotient/remainder for the top `k+1` bits of `a`. -/
lemma longDivLoop_invariant (a b m : ℕ) (hb : 0 < b) (ham : a < 2 ^ (m + 1)) :
    ∀ k, k ≤ m → let res := longDivLoop a b m k
      res.1 * b + res.2 = a / 2 ^ (m - k) ∧ res.2 < b := by
  intro k hk
  induction k with
  | zero =>
    simp only [longDivLoop, Nat.sub_zero]
    obtain ⟨heq, hr⟩ := longDivStep_invariant b (a.testBit m) 0 0 hb
    simp at heq
    refine ⟨?_, hr⟩
    rw [heq, div_pow_two_step a m, Nat.div_eq_of_lt ham]; ring
  | succ k ih =>
    simp only [longDivLoop]
    obtain ⟨heq, hr⟩ := ih (by omega : k ≤ m)
    obtain ⟨heq2, hr2⟩ := longDivStep_invariant b (a.testBit (m - k - 1)) _ _ hr
    refine ⟨?_, hr2⟩
    rw [heq2, heq]
    have hmk : m - (k + 1) = m - k - 1 := by omega
    rw [hmk, div_pow_two_step a (m - k - 1)]
    have : m - k - 1 + 1 = m - k := by omega
    rw [this]

/-- Correctness of `longDiv`: for `0 < b` and `a < 2^(m+1)`, the result `(q, r) = longDiv a b m`
satisfies `a = q * b + r` with `r < b`, i.e., it computes the integer quotient and remainder. -/
theorem long_division_correct (a b m : ℕ) (hb : 0 < b) (ham : a < 2 ^ (m + 1)) :
    let res := longDiv a b m
    a = res.1 * b + res.2 ∧ res.2 < b := by
  simp only [longDiv]
  obtain ⟨heq, hr⟩ := longDivLoop_invariant a b m hb ham m le_rfl
  simp only [Nat.sub_self, pow_zero, Nat.div_one] at heq
  exact ⟨heq.symm, hr⟩

/-- Natural-number long division specialized to the bit-length of `a`: uses `Nat.log 2 a` as the
top bit index, yielding a quotient/remainder pair for `a / b`. -/
def longDivNat (a b : ℕ) : ℕ × ℕ :=
  longDiv a b (Nat.log 2 a)

end IntegerLongDivision
