/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

namespace CoxeterSystem

open List

variable {B : Type*} {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/-- Period-$2 m(i, i')$ identity for the alternating word product:
extending an alternating word $s_i s_{i'} s_i \cdots$ by $2 m(i, i')$ extra
letters does not change its product in $W$. -/
theorem wordProd_alternatingWord_periodic (i i' : B) (n : ℕ) :
    π (alternatingWord i i' (n + M i i' * 2)) = π (alternatingWord i i' n) := by
  simp only [cs.prod_alternatingWord_eq_mul_pow]
  have hparity : Even (n + M i i' * 2) ↔ Even n := by
    constructor
    · intro ⟨k, hk⟩; exact ⟨k - M i i', by omega⟩
    · intro ⟨k, hk⟩; exact ⟨k + M i i', by omega⟩
  have hdiv : (n + M i i' * 2) / 2 = n / 2 + M i i' := by omega
  congr 1
  · by_cases h : Even n <;> simp [h, hparity.mpr, hparity] at *
  · rw [hdiv, pow_add, pow_mul_comm, cs.simple_mul_simple_pow i i', one_mul]

/-- Length bound for alternating word products in the dihedral subgroup:
$\ell(\pi(\mathtt{alternatingWord}\,i\,i'\,n)) \le m(i, i')$ whenever
$m(i, i') \ne 0$. -/
theorem length_wordProd_alternatingWord_le (i i' : B) (n : ℕ) (hM : M i i' ≠ 0) :
    ℓ (π (alternatingWord i i' n)) ≤ M i i' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  by_cases hn : n ≤ M i i' * 2
  · by_cases hn' : n ≤ M i i'
    · calc ℓ (π (alternatingWord i i' n))
          ≤ (alternatingWord i i' n).length := cs.length_wordProd_le _
        _ = n := length_alternatingWord _ _ _
        _ ≤ M i i' := hn'
    · push Not at hn'
      rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' n hn]
      calc ℓ (π (alternatingWord i' i (M i i' * 2 - n)))
          ≤ (alternatingWord i' i (M i i' * 2 - n)).length := cs.length_wordProd_le _
        _ = M i i' * 2 - n := length_alternatingWord _ _ _
        _ ≤ M i i' := by omega
  · push Not at hn
    have hlt : n - M i i' * 2 < n := by omega
    have heq : π (alternatingWord i i' n) = π (alternatingWord i i' (n - M i i' * 2)) := by
      have h := cs.wordProd_alternatingWord_periodic i i' (n - M i i' * 2)
      rwa [Nat.sub_add_cancel (le_of_lt hn)] at h
    rw [heq]
    exact ih (n - M i i' * 2) hlt

/-- Right multiplication by $s_i$ extends an alternating word
$s_i s_{i'} \cdots$ of length $n$ to an alternating word
$s_{i'} s_i \cdots$ of length $n + 1$. -/
theorem wordProd_alternatingWord_mul_simple (i i' : B) (n : ℕ) :
    π (alternatingWord i i' n) * s i = π (alternatingWord i' i (n + 1)) := by
  rw [alternatingWord_succ i' i n]
  rw [cs.wordProd_concat]

/-- Right multiplication by $s_i$ shortens an alternating word
$s_{i'} s_i \cdots$ of length $n + 1$ ending in $s_i$ to the alternating word
$s_i s_{i'} \cdots$ of length $n$. -/
theorem wordProd_alternatingWord_mul_same (i i' : B) (n : ℕ) :
    π (alternatingWord i' i (n + 1)) * s i = π (alternatingWord i i' n) := by
  have h1 : π (alternatingWord i' i (n + 1)) = π (alternatingWord i i' n) * s i := by
    rw [alternatingWord_succ i' i n, cs.wordProd_concat]
  rw [h1, mul_assoc, cs.simple_mul_simple_self, mul_one]

/-- Any word in two simple generators $s_i, s_{i'}$ has the same product as
some alternating word in those generators (starting with either letter). -/
theorem wordProd_word_in_two_generators (i i' : B) (word : List B)
    (hmem : ∀ b ∈ word, b = i ∨ b = i') :
    ∃ (n : ℕ), cs.wordProd word = π (alternatingWord i i' n) ∨
               cs.wordProd word = π (alternatingWord i' i n) := by
  induction word using List.reverseRecOn with
  | nil =>
    exact ⟨0, Or.inl (by simp [cs.wordProd_nil, alternatingWord])⟩
  | append_singleton l c ih =>
    have hc : c = i ∨ c = i' := hmem c (by simp)
    have hl : ∀ b ∈ l, b = i ∨ b = i' := fun b hb => hmem b (by simp [hb])
    obtain ⟨n, hn⟩ := ih hl
    rw [cs.wordProd_append, cs.wordProd_singleton]
    rcases hn with hL | hR
    · rcases hc with hci | hci
      · rw [hL, hci]
        exact ⟨n + 1, Or.inr (cs.wordProd_alternatingWord_mul_simple i i' n)⟩
      · rw [hL, hci]
        rcases n with _ | m
        · simp [alternatingWord, cs.wordProd_nil]
          exact ⟨1, Or.inl (by simp [alternatingWord, cs.wordProd_singleton])⟩
        · exact ⟨m, Or.inr (cs.wordProd_alternatingWord_mul_same i' i m)⟩
    · rcases hc with hci | hci
      · rw [hR, hci]
        rcases n with _ | m
        · simp [alternatingWord, cs.wordProd_nil]
          exact ⟨1, Or.inr (by simp [alternatingWord, cs.wordProd_singleton])⟩
        · exact ⟨m, Or.inl (cs.wordProd_alternatingWord_mul_same i i' m)⟩
      · rw [hR, hci]
        exact ⟨n + 1, Or.inl (cs.wordProd_alternatingWord_mul_simple i' i n)⟩

/-- Universal dihedral length bound: any word in the two simple generators
$s_i, s_{i'}$ has product of length at most $m(i, i')$. -/
theorem length_wordProd_le_M (i i' : B) (word : List B)
    (hmem : ∀ b ∈ word, b = i ∨ b = i') (hM : M i i' ≠ 0) :
    ℓ (cs.wordProd word) ≤ M i i' := by
  obtain ⟨n, hn⟩ := cs.wordProd_word_in_two_generators i i' word hmem
  rcases hn with h | h
  · rw [h]; exact cs.length_wordProd_alternatingWord_le i i' n hM
  · rw [h]
    have hM' : M i' i ≠ 0 := by rw [CoxeterMatrix.symmetric]; exact hM
    calc ℓ (π (alternatingWord i' i n))
        ≤ M i' i := cs.length_wordProd_alternatingWord_le i' i n hM'
      _ = M i i' := CoxeterMatrix.symmetric M i' i

end CoxeterSystem
