/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.Words
import Mathlib.GroupTheory.Coxeter.Length

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CoxeterSystem

variable {B : Type*} [DecidableEq B] {W : Type*} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

/-- Every letter of an alternating word $iji j \cdots$ of length $m$ equals either $i$
or $j$. -/
theorem mem_alternatingWord (i j : B) (m : ℕ) (b : B)
    (hb : b ∈ alternatingWord i j m) : b = i ∨ b = j := by
  induction m generalizing i j with
  | zero =>
    simp [show alternatingWord i j 0 = [] from rfl] at hb
  | succ n ih =>
    rw [alternatingWord_succ] at hb
    rw [List.concat_eq_append] at hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact (ih j i hb).symm
    · exact Or.inr hb

/-- Rank-2 parabolic decomposition: for every $w \in W$ and distinct $s, t \in S$, there
exist $x \in W$ and a word $y$ on the alphabet $\{s, t\}$ such that $w = x \cdot y$,
$\ell(x \cdot s) = \ell(x \cdot t) = \ell(x) + 1$, and lengths add:
$\ell(x) + \mathrm{len}(y) = \ell(w)$. -/
theorem parabolic_decomp_rank2 (w : W) (s t : B) (hst : s ≠ t) :
    ∃ (x : W) (y_word : List B),
      x * cs.wordProd y_word = w ∧
      cs.length (x * cs.simple s) = cs.length x + 1 ∧
      cs.length (x * cs.simple t) = cs.length x + 1 ∧
      (∀ b ∈ y_word, b = s ∨ b = t) ∧
      cs.length x + y_word.length = cs.length w := by

  induction h : cs.length w using Nat.strongRecOn generalizing w with
  | _ n ih =>

    rcases cs.length_mul_simple w s with hasc_s | hdesc_s
    ·
      rcases cs.length_mul_simple w t with hasc_t | hdesc_t
      ·
        exact ⟨w, [], by simp [cs.wordProd_nil], hasc_s, hasc_t,
          fun b hb => absurd hb List.not_mem_nil, by simp [h]⟩
      ·
        have hlt : cs.length (w * cs.simple t) < n := by omega
        obtain ⟨x, y_word, hprod, hxs, hxt, hmem, hlen_eq⟩ :=
          ih (cs.length (w * cs.simple t)) hlt (w * cs.simple t) rfl
        refine ⟨x, y_word ++ [t], ?_, hxs, hxt, ?_, ?_⟩
        ·
          rw [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc, hprod,
               mul_assoc, cs.simple_mul_simple_self, mul_one]
        ·
          intro b hb
          simp only [List.mem_append, List.mem_singleton] at hb
          exact hb.elim (hmem b) (fun h => Or.inr h)
        ·
          simp only [List.length_append, List.length_singleton]; omega
    ·
      have hlt : cs.length (w * cs.simple s) < n := by omega
      obtain ⟨x, y_word, hprod, hxs, hxt, hmem, hlen_eq⟩ :=
        ih (cs.length (w * cs.simple s)) hlt (w * cs.simple s) rfl
      refine ⟨x, y_word ++ [s], ?_, hxs, hxt, ?_, ?_⟩
      · rw [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc, hprod,
             mul_assoc, cs.simple_mul_simple_self, mul_one]
      · intro b hb
        simp only [List.mem_append, List.mem_singleton] at hb
        exact hb.elim (hmem b) (fun h => Or.inl h)
      · simp only [List.length_append, List.length_singleton]; omega

end CoxeterSystem
