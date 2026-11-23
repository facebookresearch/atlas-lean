/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.ContextFree
import Atlas.TheoryOfComputation.code.CFGtoPDA
import Atlas.TheoryOfComputation.code.RegularLanguages

universe u


/-- Every context-free language is recognized by some PDA. This is the converse direction of the
equivalence of CFGs and PDAs (Theorem, Lecture 4): given a CFG `g` whose language is `L`,
the constructed pushdown automaton `CFGtoPDA.toPDA g` recognizes `L`. -/
theorem cfl_recognized_by_pda {α : Type u} (L : Language α)
    (hL : Language.IsContextFree L) :
    ∃ (σ : Type u) (γ : Type u) (M : PDA α σ γ), M.language = L := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨_, _, CFGtoPDA.toPDA g, CFGtoPDA.toPDA_language g⟩

namespace PDA

variable {α : Type u} {σ₁ : Type*} {σ₂ : Type*} {γ : Type*}

/-- Product construction of a PDA `P` and a DFA `D`. The resulting PDA has state set
`σ₁ × σ₂`; it simulates `P` on its first component and the DFA `D` on its second component.
For ε-transitions of `P`, the DFA state is left unchanged; for input transitions on `a`,
the DFA component advances by `D.step _ a`. This is the standard construction used to show
that the class of CFLs is closed under intersection with regular languages. -/
def product (P : PDA α σ₁ γ) (D : DFA α σ₂) : PDA α (σ₁ × σ₂) γ where
  step := fun ⟨qp, qd⟩ a pop =>
    match a with
    | none =>
      { ⟨(qp', qd), push⟩ | (qp' : σ₁) (push : Option γ)
          (_ : (qp', push) ∈ P.step qp none pop) }
    | some a =>
      { ⟨(qp', D.step qd a), push⟩ | (qp' : σ₁) (push : Option γ)
          (_ : (qp', push) ∈ P.step qp (some a) pop) }
  start := (P.start, D.start)
  accept := P.accept ×ˢ D.accept

/-- Projection lemma: a single step of the product PDA `P.product D` projects onto a single
step of the original PDA `P` on the first component (state, input, stack). -/
theorem product_step_proj₁ (P : PDA α σ₁ γ) (D : DFA α σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
    (hs : (P.product D).Step c₁ c₂) :
    P.Step (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
  cases hs with
  | mk q q' a pop push input stack hmem =>
    obtain ⟨qp, qd⟩ := q
    simp only [product] at hmem
    cases a with
    | none =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact Step.mk qp qp' none pop push input stack hP
    | some a =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact Step.mk qp qp' (some a) pop push input stack hP

/-- DFA invariant for one step of the product PDA: every step of `P.product D`
corresponds to consuming some optional symbol `a` from the input and advancing the DFA
component by `D.evalFrom _ a.toList`. -/
theorem product_step_dfa_invariant (P : PDA α σ₁ γ) (D : DFA α σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
    (hs : (P.product D).Step c₁ c₂) :
    ∃ (a : Option α),
      c₁.2.1 = a.toList ++ c₂.2.1 ∧
      c₂.1.2 = D.evalFrom c₁.1.2 a.toList := by
  cases hs with
  | mk q q' a pop push input stack hmem =>
    obtain ⟨qp, qd⟩ := q
    simp only [product] at hmem
    cases a with
    | none =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact ⟨none, rfl, rfl⟩
    | some a =>
      obtain ⟨qp', push', hP, heq⟩ := hmem
      cases heq
      exact ⟨some a, rfl, rfl⟩

/-- Reflexive–transitive version of `product_step_proj₁`: any computation of the product
PDA `P.product D` projects to a computation of `P` on the first component. -/
theorem product_reaches_proj₁ (P : PDA α σ₁ γ) (D : DFA α σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
    (hr : (P.product D).Reaches c₁ c₂) :
    P.Reaches (c₁.1.1, c₁.2.1, c₁.2.2) (c₂.1.1, c₂.2.1, c₂.2.2) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (product_step_proj₁ P D hs)

/-- DFA invariant for a full computation of the product PDA: any reachable configuration of
`P.product D` corresponds to consuming a `consumed` prefix of the input, with the DFA component
equal to `D.evalFrom _ consumed`. -/
theorem product_reaches_dfa_invariant (P : PDA α σ₁ γ) (D : DFA α σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁ × σ₂) (γ := γ)}
    (hr : (P.product D).Reaches c₁ c₂) :
    ∃ (consumed : List α),
      c₁.2.1 = consumed ++ c₂.2.1 ∧
      c₂.1.2 = D.evalFrom c₁.1.2 consumed := by
  induction hr with
  | refl => exact ⟨[], rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨consumed₁, hinput₁, hdfa₁⟩ := ih
    obtain ⟨a, hinput_step, hdfa_step⟩ := product_step_dfa_invariant P D hs
    exact ⟨consumed₁ ++ a.toList,
      by rw [hinput₁, List.append_assoc, hinput_step],
      by rw [hdfa_step, hdfa₁]; simp [DFA.evalFrom, List.foldl_append]⟩

/-- Lifting lemma: any single step of the PDA `P` can be simulated by the product PDA
`P.product D` starting from any DFA state `qd`, with the DFA component advancing along the
symbol consumed in the step. -/
theorem product_step_lift (P : PDA α σ₁ γ) (D : DFA α σ₂)
    (qd : σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁) (γ := γ)}
    (hs : P.Step c₁ c₂) :
    ∃ (a : Option α),
      c₁.2.1 = a.toList ++ c₂.2.1 ∧
      (P.product D).Step
        ((c₁.1, qd), c₁.2.1, c₁.2.2)
        ((c₂.1, D.evalFrom qd a.toList), c₂.2.1, c₂.2.2) := by
  cases hs with
  | mk qp qp' a pop push input stack hmem =>
    refine ⟨a, rfl, Step.mk (qp, qd) (qp', D.evalFrom qd a.toList) a pop push input stack ?_⟩
    simp only [product]
    cases a with
    | none => exact ⟨qp', push, hmem, rfl⟩
    | some a => exact ⟨qp', push, hmem, rfl⟩

/-- Reflexive–transitive lifting of `product_step_lift`: any computation of `P` from `c₁` to `c₂`
can be matched, starting from any DFA state `qd`, by a corresponding computation of `P.product D`
where the DFA component evolves to `D.evalFrom qd consumed`. -/
theorem product_reaches_of_pda_reaches (P : PDA α σ₁ γ) (D : DFA α σ₂)
    (qd : σ₂)
    {c₁ c₂ : Config (α := α) (σ := σ₁) (γ := γ)}
    (hr : P.Reaches c₁ c₂) :
    ∃ (consumed : List α),
      c₁.2.1 = consumed ++ c₂.2.1 ∧
      (P.product D).Reaches
        ((c₁.1, qd), c₁.2.1, c₁.2.2)
        ((c₂.1, D.evalFrom qd consumed), c₂.2.1, c₂.2.2) := by
  induction hr with
  | refl => exact ⟨[], rfl, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    obtain ⟨consumed₁, hinput₁, hreach₁⟩ := ih
    obtain ⟨a, hinput_step, hstep_prod⟩ := product_step_lift P D (D.evalFrom qd consumed₁) hs
    refine ⟨consumed₁ ++ a.toList, ?_, ?_⟩
    · rw [hinput₁, List.append_assoc, hinput_step]
    · have : D.evalFrom (D.evalFrom qd consumed₁) a.toList =
             D.evalFrom qd (consumed₁ ++ a.toList) := by
        simp [DFA.evalFrom, List.foldl_append]
      rw [this] at hstep_prod
      exact hreach₁.tail hstep_prod

/-- Language of the product PDA: `L(P.product D) = L(P) ∩ L(D)`. This is the key step
in proving that the class of context-free languages is closed under intersection with a regular
language. -/
theorem product_language (P : PDA α σ₁ γ) (D : DFA α σ₂) :
    (P.product D).language = P.language ⊓ (D.accepts : Language α) := by
  ext w
  constructor
  ·
    intro hw
    change (P.product D).Accepts w at hw
    obtain ⟨⟨qp, qd⟩, hqacc, stack, hreach⟩ := hw
    simp only [product, Set.mem_prod] at hqacc
    constructor
    ·
      show w ∈ P.language
      exact ⟨qp, hqacc.1, stack, product_reaches_proj₁ P D hreach⟩
    ·
      obtain ⟨consumed, hinput, hdfa⟩ := product_reaches_dfa_invariant P D hreach
      simp only [product] at hinput hdfa
      have hcw : w = consumed := by simpa using hinput
      show w ∈ D.accepts
      rw [DFA.mem_accepts]
      rw [DFA.eval, hcw, ← hdfa]
      exact hqacc.2
  ·
    rintro ⟨hw_pda, hw_dfa⟩
    change (P.product D).Accepts w
    obtain ⟨qp, hqp_acc, stack, hreach_p⟩ : P.Accepts w := hw_pda
    have hw_dfa' : D.eval w ∈ D.accept := D.mem_accepts.mp hw_dfa
    obtain ⟨consumed, hinput, hreach_prod⟩ :=
      product_reaches_of_pda_reaches P D D.start hreach_p
    have hcw : w = consumed := by simpa using hinput
    subst hcw
    exact ⟨(qp, D.evalFrom D.start w), by simp only [product, Set.mem_prod]; exact ⟨hqp_acc, hw_dfa'⟩,
      stack, hreach_prod⟩

end PDA

