/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

/-- The combinatorial *ballot count* `ballotCount a b`: the number of
ways to order `a` votes for candidate A and `b` votes for candidate B so that A
strictly leads B throughout the counting. It is defined by the natural
recurrence at the boundary between the +1 and -1 partial sums: zero when
`a = 0`, one when `b = 0` (any ordering of all-A votes is valid), and
`ballotCount a (b+1) + ballotCount (a+1) b` when `a > b`. -/
def ballotCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ a, Nat.succ b =>
    if Nat.succ a > Nat.succ b then
      ballotCount a (Nat.succ b) + ballotCount (Nat.succ a) b
    else 0

/-- Boundary case: with zero votes for A, no valid sequence can have A
strictly leading, so `ballotCount 0 b = 0`. -/
@[simp]
theorem ballotCount_zero_left (b : ℕ) : ballotCount 0 b = 0 := by
  simp [ballotCount]

/-- Boundary case: with at least one A vote and no B votes, the unique ordering
(all A's) keeps A in the lead, so `ballotCount (a+1) 0 = 1`. -/
@[simp]
theorem ballotCount_succ_zero (a : ℕ) : ballotCount (a + 1) 0 = 1 := by
  simp [ballotCount]

/-- If A has at most as many votes as B (`a ≤ b`), then no ordering can keep A
strictly ahead throughout, so `ballotCount a b = 0`. -/
theorem ballotCount_le {a b : ℕ} (h : a ≤ b) : ballotCount a b = 0 := by
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => omega
    | succ b => simp only [ballotCount]; rw [if_neg]; omega

/-- A *ballot sequence* with `a` A-votes and `b` B-votes: a list of `±1`s of
length `a + b` containing exactly `a` ones and `b` negative ones. Each `+1`
represents a vote for candidate A, each `-1` a vote for B. -/
def IsBallotSeq (a b : ℕ) (l : List Int) : Prop :=
  l.length = a + b ∧
  l.count 1 = a ∧
  l.count (-1) = b ∧
  (∀ v ∈ l, v = 1 ∨ v = -1)

open Classical in
/-- The set of *favorable* ballot sequences for the parameters `a, b`: all
permutations of a list with `a` ones and `b` negative ones such that every
non-empty prefix has strictly positive sum (i.e. candidate A is ahead at every
intermediate counting step). -/
noncomputable def favorableSequences (a b : ℕ) : Finset (List Int) :=
  ((List.replicate a (1 : Int) ++ List.replicate b (-1 : Int)).permutations.toFinset).filter
    (fun l => ∀ k : Fin (a + b), 0 < (l.take (k.val + 1)).sum)


/-- **Ballot Theorem (integer form).** If candidate A receives `a` votes and
candidate B receives `b < a` votes, then the number of vote orderings in which
A is strictly ahead throughout the count, times the total number of votes,
equals `(a - b)` times the number of orderings of the votes:
`ballotCount a b * (a + b) = (a - b) * C(a + b, a)`. This is the combinatorial
content of the classical Bertrand ballot theorem (Durrett, Lecture 23). -/
theorem ballot_theorem (a b : ℕ) (hab : a > b) :
    ballotCount a b * (a + b) = (a - b) * Nat.choose (a + b) a := by
  induction a, b using ballotCount.induct with
  | case1 b => omega
  | case2 a => simp [Nat.choose_self]
  | case3 a b hgt ih1 ih2 =>
    simp only [ballotCount, hgt, ↓reduceIte]
    by_cases hab2 : a > b + 1
    ·
      have ih_left := ih1 hab2
      have ih_right := ih2 (by omega : a + 1 > b)
      rw [show a + (b + 1) = a + 1 + b from by omega] at ih_left
      set n := a + 1 + b with hn_def
      rw [show a + 1 + (b + 1) = n + 1 from by omega]

      apply Nat.eq_of_mul_eq_mul_right (show 0 < n from by omega)
      apply Nat.eq_of_mul_eq_mul_right (show 0 < a + 1 from by omega)

      have ratio_nat : (b + 1) * Nat.choose n a = (a + 1) * Nat.choose n (a + 1) := by
        nlinarith [Nat.add_one_mul_choose_eq n a, Nat.choose_succ_succ n a]
      have succ_mul_nat := Nat.add_one_mul_choose_eq n a

      zify [show b + 1 ≤ a from by omega,
            show b ≤ a + 1 from by omega,
            show b + 1 ≤ a + 1 from by omega] at ih_left ih_right ratio_nat succ_mul_nat ⊢

      have hfn : (↑(ballotCount a (b + 1)) : ℤ) * ↑n * (↑a + 1) =
          (↑a - ↑b - 1) * ↑(Nat.choose n a) * (↑a + 1) := by
        linear_combination (↑a + 1) * ih_left
      have hgn : (↑(ballotCount (a + 1) b) : ℤ) * ↑n * (↑a + 1) =
          (↑a + 1 - ↑b) * (↑b + 1) * ↑(Nat.choose n a) := by
        linear_combination (↑a + 1) * ih_right - (↑a + 1 - ↑b) * ratio_nat


      have key : (↑(ballotCount a (b + 1)) + ↑(ballotCount (a + 1) b) : ℤ) * ↑n * (↑a + 1) =
          (↑a - ↑b) * ↑n * ↑(Nat.choose n a) := by
        have : (↑a - ↑b - 1) * ((↑a : ℤ) + 1) + (↑a + 1 - ↑b) * (↑b + 1) = (↑a - ↑b) * ↑n := by
          simp only [hn_def]; push_cast; ring
        nlinarith [hfn, hgn]
      linear_combination (↑n + 1) * key + (↑a - ↑b) * ↑n * succ_mul_nat
    ·
      have hab_eq : a = b + 1 := by omega
      subst hab_eq
      rw [ballotCount_le (le_refl _), zero_add]

      have ih := ih2 (by omega : b + 1 + 1 > b)
      have hih : ballotCount (b + 2) b * (2 * (b + 1)) =
          2 * Nat.choose (2 * (b + 1)) (b + 2) := by
        rw [show b + 1 + 1 + b = 2 * (b + 1) from by omega,
            show b + 1 + 1 - b = 2 from by omega] at ih
        linarith
      suffices ballotCount (b + 2) b * (2 * b + 3) = Nat.choose (2 * b + 3) (b + 2) by
        rw [show b + 1 + 1 + (b + 1) = 2 * b + 3 from by omega,
            show b + 1 + 1 - (b + 1) = 1 from by omega, one_mul]
        exact this

      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * (b + 1) from by omega)
      have choose_sym : Nat.choose (2 * (b + 1)) (b + 2) = Nat.choose (2 * (b + 1)) b :=
        Nat.choose_symm_of_eq_add (by omega)
      have succ_mul_id : (2 * b + 3) * Nat.choose (2 * (b + 1)) b =
          Nat.choose (2 * b + 3) (b + 1) * (b + 1) := by
        have h := Nat.add_one_mul_choose_eq (2 * (b + 1)) b
        convert h using 2
      have choose_sym2 : Nat.choose (2 * b + 3) (b + 1) = Nat.choose (2 * b + 3) (b + 2) :=
        Nat.choose_symm_of_eq_add (by omega)
      nlinarith [choose_sym, succ_mul_id, choose_sym2]
  | case4 a b hle => omega

/-- **Ballot Theorem (probability form).** With `a > b ≥ 0` votes for A and B,
the probability that A is strictly ahead throughout the counting—the ratio of
favorable orderings to all orderings—equals `(a - b)/(a + b)`. This is the
quotient version of `ballot_theorem`. -/
theorem ballot_theorem_div (a b : ℕ) (hab : a > b) :
    (ballotCount a b : ℚ) / Nat.choose (a + b) a = ((a : ℚ) - b) / (a + b) := by
  have hab_sum_pos : (0 : ℚ) < a + b := by exact_mod_cast (show 0 < a + b by omega)
  have hchoose_pos : (0 : ℚ) < Nat.choose (a + b) a := by
    exact_mod_cast Nat.choose_pos (by omega : a ≤ a + b)
  rw [div_eq_div_iff (ne_of_gt hchoose_pos) (ne_of_gt hab_sum_pos)]
  calc (ballotCount a b : ℚ) * (↑a + ↑b)
      = ↑(ballotCount a b * (a + b)) := by push_cast; ring
    _ = ↑((a - b) * Nat.choose (a + b) a) := by exact_mod_cast ballot_theorem a b hab
    _ = (↑a - ↑b) * ↑(Nat.choose (a + b) a) := by push_cast [Nat.cast_sub (by omega : b ≤ a)]; ring
