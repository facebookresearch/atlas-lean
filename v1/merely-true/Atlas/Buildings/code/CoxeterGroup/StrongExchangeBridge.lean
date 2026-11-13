/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring

open CoxeterExchange CoxeterGroup CoxeterExchangeGenuine

namespace StrongExchangeBridge

variable {W : Type*} [Group W] {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {cs : CoxeterSystem M W}

/-- Exchange via erase-index: when $s$ is a right descent of a reduced word $w$, there is an
index $i$ such that erasing it yields a reduced word with product $w \cdot s$. -/
@[deprecated "Use exchange_descent_eraseIdx_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exchange_descent_eraseIdx
    (hsce : SignChangeExchangeHyp M cs)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
    ∃ i : Fin word.length,
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s ∧
      cs.IsReduced (word.eraseIdx i) := by
  have hex := exchange_condition_from_neg_of_descent M cs hsce
  obtain ⟨i, hi_eq⟩ := hex word s hred hdesc
  refine ⟨i, hi_eq, ?_⟩
  unfold CoxeterSystem.IsReduced
  rw [hi_eq]
  have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
    List.length_eraseIdx_of_lt i.isLt
  rw [hlen_erased]
  unfold CoxeterSystem.IsReduced at hred
  rcases cs.length_mul_simple (cs.wordProd word) s with h | h
  · omega
  · omega

/-- Existence of a reduced word ending in $s$: if $s$ is a right descent of a reduced word $w$,
there is a reduced word $w' \cdot s$ of the same product. -/
@[deprecated "Use exists_reduced_ending_in_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exists_reduced_ending_in
    (hsce : SignChangeExchangeHyp M cs)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
    ∃ (prefix_word : List B),
      cs.IsReduced (prefix_word ++ [s]) ∧
      cs.wordProd (prefix_word ++ [s]) = cs.wordProd word ∧
      prefix_word.length + 1 = word.length := by
  have hex := exchange_condition_from_neg_of_descent M cs hsce
  obtain ⟨i, hi_eq⟩ := hex word s hred hdesc
  refine ⟨word.eraseIdx i, ?_, ?_, ?_⟩
  ·
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_append, cs.wordProd_singleton, hi_eq, mul_assoc,
        cs.simple_mul_simple_self, mul_one,
        List.length_append, List.length_singleton]
    have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
      List.length_eraseIdx_of_lt i.isLt
    rw [hlen_erased]
    unfold CoxeterSystem.IsReduced at hred
    omega
  ·
    rw [cs.wordProd_append, cs.wordProd_singleton, hi_eq, mul_assoc,
        cs.simple_mul_simple_self, mul_one]
  ·
    have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
      List.length_eraseIdx_of_lt i.isLt
    rw [hlen_erased]
    have hword_pos : word.length > 0 := by
      unfold CoxeterSystem.IsReduced at hred; omega
    omega

/-- If $s$ is a right descent of $w$, then $w$ has a reduced word ending in $s$. -/
theorem exists_reduced_word_ending_in_descent
    (w : W) (s : B)
    (hdesc : cs.length (w * cs.simple s) < cs.length w) :
    ∃ (prefix_word : List B),
      cs.IsReduced (prefix_word ++ [s]) ∧
      cs.wordProd (prefix_word ++ [s]) = w := by

  obtain ⟨ω, hωred, hωprod⟩ := cs.exists_reduced_word (w * cs.simple s)
  have hωlen : ω.length = cs.length (w * cs.simple s) := by rw [hωprod]; exact hωred.symm

  refine ⟨ω, ?_, ?_⟩
  ·
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hωprod, mul_assoc,
        cs.simple_mul_simple_self, mul_one,
        List.length_append, List.length_singleton]

    rcases cs.length_mul_simple w s with h | h
    · omega
    · omega
  ·
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hωprod, mul_assoc,
        cs.simple_mul_simple_self, mul_one]

end StrongExchangeBridge
