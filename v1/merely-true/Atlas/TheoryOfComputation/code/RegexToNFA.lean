/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.RegularLanguages
import Mathlib.Computability.RegularExpressions

open Computability Language

namespace RegularLanguages

/-- Once the 3-state DFA used in `isRegular_char` enters the "sink" state `2`,
it stays there: folding the transition function over any list `l` starting at
state `2` returns `2`. -/
lemma foldl_sink {α : Type*} [DecidableEq α] (a₀ : α) (l : List α) :
    List.foldl (fun (s : Fin 3) (c : α) => if s = 0 ∧ c = a₀ then 1 else 2) 2 l = 2 := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons, show ¬((2 : Fin 3) = 0) from by omega, false_and, ↓reduceIte]
    exact ih

/-- Folding the constant-`false` transition over any list starting at `false`
yields `false`; used as a sink-state lemma for the `ε` automaton in
`isRegular_epsilon`. -/
lemma foldl_bool_sink {α : Type*} (l : List α) :
    List.foldl (fun (_ : Bool) (_ : α) => false) false l = false := by
  induction l with | nil => rfl | cons _ _ ih => exact ih

/-- The empty language `∅` (a.k.a. `0`) is regular: a one-state DFA with no
accept states recognizes it. -/
lemma isRegular_empty {α : Type*} : (0 : Language α).IsRegular := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, ?_⟩
  ext w; constructor
  · intro h; exfalso; rw [DFA.mem_accepts] at h; exact absurd h (Set.notMem_empty _)
  · intro h; exfalso; exact absurd h (by change w ∉ (∅ : Set _); exact Set.notMem_empty _)

/-- The language `{ε}` containing only the empty string (a.k.a. `1`) is
regular: a two-state DFA with start state `true ∈ F` and a sink state `false`
recognizes it. -/
lemma isRegular_epsilon {α : Type*} : (1 : Language α).IsRegular := by

  refine ⟨Bool, inferInstance, ⟨fun _ _ => false, true, {true}⟩, ?_⟩
  ext w; rw [DFA.mem_accepts]; simp only [Set.mem_singleton_iff, DFA.eval, DFA.evalFrom]
  rw [Language.mem_one]
  constructor
  · intro h; cases w with
    | nil => rfl
    | cons a t =>
      exfalso; simp only [List.foldl_cons] at h
      rw [foldl_bool_sink] at h; exact Bool.false_ne_true h
  · rintro rfl; rfl

/-- The singleton language `{[a₀]}` containing only the length-one string `a₀`
is regular: a three-state DFA with states `0` (start), `1` (accept), `2` (sink)
and the obvious transitions recognizes it. -/
lemma isRegular_char {α : Type*} [DecidableEq α] (a₀ : α) :
    ({[a₀]} : Language α).IsRegular := by
  let step : Fin 3 → α → Fin 3 := fun s a => if s = 0 ∧ a = a₀ then 1 else 2
  refine ⟨Fin 3, inferInstance, ⟨step, 0, {1}⟩, ?_⟩
  ext w
  simp only [DFA.mem_accepts, Set.mem_singleton_iff, DFA.eval, DFA.evalFrom]
  constructor
  · intro h; cases w with
    | nil => simp only [List.foldl_nil] at h; omega
    | cons b t =>
      simp only [List.foldl_cons, step] at h
      split_ifs at h with hba
      · obtain ⟨-, rfl⟩ := hba
        cases t with
        | nil => rfl
        | cons d u =>
          exfalso
          simp only [List.foldl_cons, show ¬((1 : Fin 3) = 0) from by omega,
            false_and, ↓reduceIte] at h
          rw [foldl_sink] at h; omega
      · exfalso; rw [foldl_sink] at h; omega
  · intro h; rw [h]; show List.foldl step (step 0 a₀) [] = 1
    simp [step]

/-- **Regular expressions to regular languages.**

For any regular expression `R` over `α`, the language `L(R) = R.matches'` is
regular. The proof is by structural induction on `R`, using the base cases
`isRegular_empty`, `isRegular_epsilon`, `isRegular_char` and the closure
theorems `IsRegular.add` (union), `regular_concat` (concatenation), and
`regular_star` (Kleene star).

This corresponds to Sipser's theorem: *If `R` is a regular expression and
`A = L(R)` then `A` is regular.* -/
theorem regex_language_isRegular {α : Type*} [DecidableEq α] (R : RegularExpression α) :
    R.matches'.IsRegular := by
  induction R with
  | zero => exact isRegular_empty
  | epsilon => exact isRegular_epsilon
  | char a => exact isRegular_char a
  | plus P Q ihP ihQ =>
    simp only [RegularExpression.matches']
    exact ihP.add ihQ
  | comp P Q ihP ihQ =>
    simp only [RegularExpression.matches']
    exact regular_concat ihP ihQ
  | star P ihP =>
    simp only [RegularExpression.matches']
    exact regular_star ihP

end RegularLanguages
