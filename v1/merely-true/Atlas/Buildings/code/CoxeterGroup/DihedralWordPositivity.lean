/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity
import Atlas.Buildings.code.CoxeterGroup.DihedralLengthBound
import Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Atlas.Buildings.code.CoxeterGroup.ParabolicDecomp

open Finset BigOperators CoxeterGroup CoxeterSystem

namespace CoxeterGroup

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The alternating word $s\,t\,s\,t\,\cdots$ in two distinct generators has
no two consecutive equal letters: it is a $\mathtt{Chain'}$ for $(\ne)$. -/
theorem alternatingWord_chain' (s t : B) (hst : s ≠ t) (n : ℕ) :
    List.Chain' (· ≠ ·) (alternatingWord s t n) := by
  induction n with
  | zero => exact List.IsChain.nil
  | succ m ih =>
    rw [alternatingWord_succ']
    apply List.IsChain.cons ih
    intro y hy
    match m, ih, hy with
    | 0, _, hy => simp [alternatingWord] at hy
    | k + 1, _, hy =>
      rw [alternatingWord_succ'] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      by_cases hk : Even k
      · have hk1 : ¬Even (k + 1) := fun h => (Nat.even_add_one.mp h) hk
        simp only [if_pos hk, if_neg hk1]
        exact hst
      · have hk1 : Even (k + 1) := Nat.even_add_one.mpr hk
        simp only [if_neg hk, if_pos hk1]
        exact hst.symm

/-- The alternating word $s\,t\,s\,t\,\cdots$ either is empty or ends in
$t$ (since each step in the recursion of $\mathtt{alternatingWord}$ appends
$t$ at the right). -/
theorem alternatingWord_last_cond (s t : B) (n : ℕ) :
    alternatingWord s t n = [] ∨
    (∃ h : alternatingWord s t n ≠ [], (alternatingWord s t n).getLast h = t) := by
  cases n with
  | zero => left; rfl
  | succ m =>
    right
    have heq : alternatingWord s t (m + 1) = (alternatingWord t s m).concat t :=
      alternatingWord_succ s t m
    have hne : alternatingWord s t (m + 1) ≠ [] := by
      rw [heq]; simp [List.concat_eq_append]
    refine ⟨hne, ?_⟩
    have key : (alternatingWord s t (m + 1)).getLast hne =
               ((alternatingWord t s m) ++ [t]).getLast (by simp) := by
      congr 1
      simp [heq, List.concat_eq_append]
    simp [key]

/-- Positivity of the dihedral iterate along an alternating word: for any
$n < m(s, t)$ (or $m(s, t) = \infty$), the action of the alternating word
$\mathtt{alternatingWord}\,s\,t\,n$ on $e_s$ via $\sigma$ produces a positive
root. -/
theorem alternatingWord_pos (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) (n : ℕ)
    (hlen : n < M s t ∨ M s t = 0) :
    IsPositive (wordSigma M (alternatingWord s t n) (e s)) := by
  apply parabolic_pos M s t hst (alternatingWord s t n)
  · exact CoxeterSystem.mem_alternatingWord s t n
  · rcases hlen with hlt | hm0
    · left; rwa [length_alternatingWord]
    · right; exact hm0
  · exact alternatingWord_chain' s t hst n
  · exact alternatingWord_last_cond s t n

set_option linter.unusedVariables false in
/-- Generalisation to arbitrary words in two generators: any word whose
product equals that of some alternating word of admissible length yields a
positive iterate of $e_s$ under $\mathtt{wordSigma}$. -/
theorem wordSigma_pos_of_word_in_two (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (s t : B) (hst : s ≠ t)
    (word : List B) (hmem : ∀ b ∈ word, b = s ∨ b = t)
    (hlen : cs.length (cs.wordProd word) < M s t ∨ M s t = 0)
    (hform : ∃ n, cs.wordProd word = cs.wordProd (alternatingWord s t n) ∧
                   (n < M s t ∨ M s t = 0)) :
    IsPositive (wordSigma M word (e s)) := by
  obtain ⟨n, hprod_eq, hn_bound⟩ := hform
  have h := wordSigma_eq_of_wordProd_eq M cs word (alternatingWord s t n) hprod_eq (e s)
  rw [h]
  exact alternatingWord_pos M s t hst n hn_bound

end CoxeterGroup
