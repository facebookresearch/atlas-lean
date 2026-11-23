/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.CFLInterRegular
import Atlas.TheoryOfComputation.code.RegularLanguages

universe u

namespace RegularIsCFL

open Computability

/-- Convert a DFA `D` to a PDA over the same input alphabet that ignores its
stack (using a trivial stack alphabet `PUnit`). The PDA's transition mirrors
`D.step` on real input symbols and has no ε-transitions or stack moves. -/
def dfaToPDA {α : Type u} {σ : Type*} (D : DFA α σ) : PDA α σ PUnit where
  step := fun q a pop =>
    match a, pop with
    | some a, none => {(D.step q a, none)}
    | _, _ => ∅
  start := D.start
  accept := D.accept

variable {α : Type u} {σ : Type*}

/-- Any one-step transition of `dfaToPDA D` consumes a single input symbol `a`,
moves the DFA state via `D.step`, and leaves the stack unchanged. -/
lemma dfaToPDA_step_characterize (D : DFA α σ) {c₁ c₂ : σ × List α × List PUnit}
    (h : (dfaToPDA D).Step c₁ c₂) :
    ∃ a : α, c₁.2.1 = a :: c₂.2.1 ∧ c₂.1 = D.step c₁.1 a ∧ c₂.2.2 = c₁.2.2 := by
  obtain ⟨q₁, w₁, s₁⟩ := c₁
  obtain ⟨q₂, w₂, s₂⟩ := c₂
  simp only
  cases h with
  | mk _ _ a pop push input stack hmem =>
    simp only [dfaToPDA] at hmem
    split at hmem
    · rename_i a
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨a, by simp [Option.toList], rfl, rfl⟩
    · exact absurd hmem (Set.notMem_empty _)

/-- Starting from any DFA state `q` with input `w` and empty stack, the PDA
`dfaToPDA D` reaches the configuration `(D.evalFrom q w, [], [])` after
consuming the entire input. -/
lemma dfaToPDA_reaches_evalFrom (D : DFA α σ) (q : σ) (w : List α) :
    (dfaToPDA D).Reaches (q, w, []) (D.evalFrom q w, [], []) := by
  induction w generalizing q with
  | nil =>
    exact Relation.ReflTransGen.refl
  | cons a w ih =>
    apply Relation.ReflTransGen.head
    · have hmem : (D.step q a, (none : Option PUnit)) ∈
          (dfaToPDA D).step q (some a) none := by
        simp [dfaToPDA]
      exact PDA.Step.mk q (D.step q a) (some a) none none w [] hmem
    · exact ih (D.step q a)

/-- Inverse direction: any reachable configuration of `dfaToPDA D` from an
empty-stack start has empty stack, and the consumed input is a prefix of the
remaining input that drives `D.evalFrom` from the start to the current state. -/
lemma dfaToPDA_reaches_inv (D : DFA α σ)
    {c₁ c₂ : σ × List α × List PUnit}
    (hreach : (dfaToPDA D).Reaches c₁ c₂)
    (hs : c₁.2.2 = []) :
    c₂.2.2 = [] ∧ ∃ pref : List α,
      c₁.2.1 = pref ++ c₂.2.1 ∧ c₂.1 = D.evalFrom c₁.1 pref := by
  induction hreach with
  | refl =>
    exact ⟨hs, [], by simp [DFA.evalFrom]⟩
  | tail _ hstep ih =>
    obtain ⟨hs_mid, pref, hw_mid, hq_mid⟩ := ih
    obtain ⟨a, hw_step, hq_step, hs_step⟩ := dfaToPDA_step_characterize D hstep
    refine ⟨hs_step ▸ hs_mid, pref ++ [a], ?_, ?_⟩
    · rw [hw_mid, List.append_assoc, List.singleton_append, hw_step]
    · simp [DFA.evalFrom, List.foldl_append, hq_mid, hq_step]

/-- The PDA `dfaToPDA D` recognizes exactly the language of the DFA `D`. -/
theorem dfaToPDA_language (D : DFA α σ) :
    (dfaToPDA D).language = D.accepts := by
  ext w
  simp only [PDA.language, PDA.Accepts, DFA.mem_accepts]
  constructor
  ·
    rintro ⟨q, hq, stack, hreach⟩
    obtain ⟨_, pref, hw_eq, hq_eq⟩ := dfaToPDA_reaches_inv D hreach rfl


    change q = D.evalFrom D.start pref at hq_eq
    change w = pref ++ [] at hw_eq
    simp only [List.append_nil] at hw_eq
    simp only [dfaToPDA] at hq
    subst hw_eq; subst hq_eq
    exact hq
  ·
    intro haccept
    exact ⟨D.eval w, haccept, [], dfaToPDA_reaches_evalFrom D D.start w⟩


end RegularIsCFL
