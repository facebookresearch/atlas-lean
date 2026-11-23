/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.ContextFree

universe u_pda

namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

/-- A language `A ⊆ Σ*` is PDA-recognizable if there exist state and stack alphabet types
together with a pushdown automaton `P = (Q, Σ, Γ, δ, q₀, F)` whose accepted language equals `A`. -/
def IsPDARecognizable (A : Language T) : Prop :=
  ∃ (σ : Type u_pda) (γ : Type u_pda) (P : PDA T σ γ), P.language = A

/-- States of the PDA constructed from a CFG. The PDA has four kinds of states:
* `start` — initial state; pushes the start variable and the bottom-of-stack marker;
* `loop` — main loop that either pops a terminal matching the input, applies a rule
  by replacing a nonterminal on the stack, or transitions to `accept` when the
  bottom-of-stack marker is seen;
* `pushing L` — intermediate states used to push a list `L` of grammar symbols onto
  the stack one symbol per step;
* `accept` — the unique accepting state. -/
inductive QState (T : Type*) (N : Type) where
  | start | loop | pushing : List (Symbol T N) → QState T N | accept

/-- The standard PDA construction from a CFG `g` (Sipser, Lecture 4, "Converting CFGs to PDAs").
The stack alphabet is `Option (Symbol T g.NT)`, where `none` is the bottom-of-stack marker
and `some s` carries a grammar symbol `s`. The PDA:
1. From `start`, pushes the bottom marker and moves into `pushing [S]` where `S = g.initial`.
2. In `loop`, pops a nonterminal `A` and nondeterministically replaces it by the right-hand
   side of any rule `A → r.output` (using the `pushing` states to push symbols one at a time).
3. In `loop`, pops a terminal `t` from the stack only if the next input symbol matches `t`.
4. When the bottom marker is exposed in `loop`, moves to `accept`. -/
def toPDA (g : ContextFreeGrammar T) :
    PDA T (QState T g.NT) (Option (Symbol T g.NT)) where
  start := QState.start
  accept := {QState.accept}
  step := fun q a pop =>
    match q, a, pop with
    | QState.start, none, none =>
        {(QState.pushing [Symbol.nonterminal g.initial], some none)}
    | QState.loop, none, some (some (Symbol.nonterminal A)) =>
        { p | ∃ r ∈ g.rules, r.input = A ∧
          p = (QState.pushing r.output.reverse, none) }
    | QState.loop, some a, some (some (Symbol.terminal t)) =>
        { p | a = t ∧ p = (QState.loop, none) }
    | QState.loop, none, some none =>
        {(QState.accept, none)}
    | QState.pushing (s :: rest), none, none =>
        {(QState.pushing rest, some (some s))}
    | QState.pushing [], none, none =>
        {(QState.loop, none)}
    | _, _, _ => ∅

variable {g : ContextFreeGrammar T}

set_option maxRecDepth 1024 in
/-- From state `pushing L` on stack `stack`, the PDA can reach state `loop` having pushed
all symbols of `L` onto the stack (resulting in `L.reverse.map some ++ stack`), without
consuming any input. -/
lemma toPDA_push_list
    (L : List (Symbol T g.NT)) (input : List T)
    (stack : List (Option (Symbol T g.NT))) :
    (toPDA g).Reaches (QState.pushing L, input, stack)
      (QState.loop, input, L.reverse.map some ++ stack) := by
  induction L generalizing stack with
  | nil =>
    simp only [List.reverse_nil, List.map_nil, List.nil_append]
    apply Relation.ReflTransGen.single
    have h := PDA.Step.mk (M := toPDA g) (QState.pushing []) QState.loop
      (none : Option T) (none : Option (Option (Symbol T g.NT))) none input stack
      (by simp [toPDA])
    simpa [Option.toList] using h
  | cons s rest ih =>
    apply Relation.ReflTransGen.head
    · have h := PDA.Step.mk (M := toPDA g) (QState.pushing (s :: rest)) (QState.pushing rest)
        (none : Option T) (none : Option (Option (Symbol T g.NT))) (some (some s)) input stack
        (by simp [toPDA])
      simpa [Option.toList] using h
    · simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] at *
      exact ih _

set_option maxRecDepth 1024 in
/-- In `loop`, the PDA can pop a terminal `t` from the top of the stack while
consuming a matching input symbol `t`. -/
lemma toPDA_pop_terminal (t : T) (input : List T)
    (stack : List (Option (Symbol T g.NT))) :
    (toPDA g).Reaches (QState.loop, t :: input, some (Symbol.terminal t) :: stack)
      (QState.loop, input, stack) := by
  apply Relation.ReflTransGen.single
  have h := PDA.Step.mk (M := toPDA g) QState.loop QState.loop
    (some t) (some (some (Symbol.terminal t))) none input stack (by simp [toPDA])
  simpa [Option.toList] using h

set_option maxRecDepth 1024 in
/-- In `loop`, if a nonterminal `r.input` is on top of the stack and `r ∈ g.rules` is a
production with that left-hand side, the PDA can replace the nonterminal by `r.output`
(reaching state `loop` with `r.output.map some ++ stack` on the stack). -/
lemma toPDA_apply_rule (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules)
    (input : List T) (stack : List (Option (Symbol T g.NT))) :
    (toPDA g).Reaches (QState.loop, input, some (Symbol.nonterminal r.input) :: stack)
      (QState.loop, input, r.output.map some ++ stack) := by
  apply Relation.ReflTransGen.head
  · have h := PDA.Step.mk (M := toPDA g) QState.loop (QState.pushing r.output.reverse)
      (none : Option T) (some (some (Symbol.nonterminal r.input))) none input stack
      (show _ ∈ _ from ⟨r, hr, rfl, rfl⟩)
    simpa [Option.toList] using h
  · have h := toPDA_push_list r.output.reverse input stack
    simp only [List.reverse_reverse] at h
    convert h using 2


/-- `DerivesIn' g n γ δ` means `γ ⇒ⁿ δ` in `g`: there is a derivation of length exactly
`n` from `γ` to `δ` using the rules of `g`. -/
inductive DerivesIn' (g : ContextFreeGrammar T) :
    ℕ → List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  | refl (γ) : DerivesIn' g 0 γ γ
  | step {n γ δ τ} : g.Produces γ δ → DerivesIn' g n δ τ → DerivesIn' g (n + 1) γ τ

/-- A zero-step derivation forces the start and end sentential forms to be equal. -/
lemma derivesIn'_zero_eq {γ δ : List (Symbol T g.NT)}
    (h : DerivesIn' g 0 γ δ) : γ = δ := by cases h; rfl

/-- Append a single derivation step at the end: if `γ ⇒ⁿ mid` and `mid ⇒ δ`,
then `γ ⇒^{n+1} δ`. -/
lemma derivesIn'_snoc {n : ℕ} {γ mid δ : List (Symbol T g.NT)}
    (h : DerivesIn' g n γ mid) (hp : g.Produces mid δ) : DerivesIn' g (n + 1) γ δ := by
  induction h with
  | refl => exact DerivesIn'.step hp (DerivesIn'.refl _)
  | step hprod _ ih => exact DerivesIn'.step hprod (ih hp)

/-- Any derivation `γ ⇒* δ` can be witnessed by a derivation of some explicit finite length `n`. -/
lemma derives_to_derivesIn' {γ δ : List (Symbol T g.NT)}
    (h : g.Derives γ δ) : ∃ n, DerivesIn' g n γ δ := by
  induction h with
  | refl => exact ⟨0, DerivesIn'.refl _⟩
  | tail _ hprod ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, derivesIn'_snoc hn hprod⟩

/-- If a single derivation step is applied to `(terminal t) :: γ'`, the leading terminal
is preserved: the result is `(terminal t) :: δ'` where `γ' ⇒ δ'`. -/
lemma produces_cons_terminal {t : T} {γ' δ : List (Symbol T g.NT)}
    (h : g.Produces (Symbol.terminal t :: γ') δ) :
    ∃ δ', δ = Symbol.terminal t :: δ' ∧ g.Produces γ' δ' := by
  obtain ⟨r, hr_mem, hr_rew⟩ := h
  rw [ContextFreeRule.rewrites_iff] at hr_rew
  obtain ⟨p, q, hpq1, hpq2⟩ := hr_rew
  cases p with
  | nil => simp at hpq1
  | cons x p' =>
    simp at hpq1; obtain ⟨rfl, rfl⟩ := hpq1
    refine ⟨p' ++ r.output ++ q, ?_, ⟨r, hr_mem, ?_⟩⟩
    · simp [hpq2]
    · convert ContextFreeRule.rewrites_of_exists_parts r p' q using 1; simp

/-- Iterated version of `produces_cons_terminal`: in an `n`-step derivation starting from
`(terminal t) :: γ'`, the leading terminal is preserved throughout, and the suffix admits
a matching `n`-step derivation. -/
lemma derivesIn'_cons_terminal {n : ℕ} {t : T} {γ' δ : List (Symbol T g.NT)}
    (h : DerivesIn' g n (Symbol.terminal t :: γ') δ) :
    ∃ δ', δ = Symbol.terminal t :: δ' ∧ DerivesIn' g n γ' δ' := by
  induction n generalizing γ' δ with
  | zero => cases h with | refl => exact ⟨γ', rfl, DerivesIn'.refl _⟩
  | succ n ih =>
    cases h with
    | step hprod hrest =>
      obtain ⟨v', rfl, hprod'⟩ := produces_cons_terminal hprod
      obtain ⟨δ', rfl, hδ'⟩ := ih hrest
      exact ⟨δ', rfl, DerivesIn'.step hprod' hδ'⟩

/-- A derivation starting from the empty sentential form must be a zero-step derivation
and end at the empty sentential form. -/
lemma derivesIn'_nil_inv {n : ℕ} {δ : List (Symbol T g.NT)}
    (h : DerivesIn' g n ([] : List (Symbol T g.NT)) δ) : n = 0 ∧ δ = [] := by
  cases n with
  | zero => cases h with | refl => exact ⟨rfl, rfl⟩
  | succ n =>
    cases h with | step hprod _ =>
      obtain ⟨r, _, hr_rew⟩ := hprod
      rw [ContextFreeRule.rewrites_iff] at hr_rew
      obtain ⟨p, _, hpq, _⟩ := hr_rew; simp at hpq

/-- Reordering derivations to apply the leftmost nonterminal first.
If `A :: γ' ⇒^{n+1} target` and `target` is a string of terminals, then some rule
`r ∈ g.rules` with `r.input = A` is applied (effectively first) and `r.output ++ γ' ⇒^m target`
for some `m ≤ n`. -/
lemma leftmost_step_n (n : ℕ) (A : g.NT) (γ' target : List (Symbol T g.NT))
    (h : DerivesIn' g (n + 1) (Symbol.nonterminal A :: γ') target)
    (h_target : ∀ s ∈ target, ∃ t, s = Symbol.terminal t) :
    ∃ r ∈ g.rules, r.input = A ∧
      ∃ m, m ≤ n ∧ DerivesIn' g m (r.output ++ γ') target := by
  induction n generalizing A γ' target with
  | zero =>
    cases h with | step hprod hrest =>
    have hv_eq := derivesIn'_zero_eq hrest; subst hv_eq
    obtain ⟨r, hr_mem, hr_rew⟩ := hprod
    rw [ContextFreeRule.rewrites_iff] at hr_rew
    obtain ⟨p, q, hu_eq, hv_eq⟩ := hr_rew
    cases p with
    | nil =>
      simp at hu_eq; obtain ⟨hA, hq⟩ := hu_eq; subst hq; subst hA
      exact ⟨r, hr_mem, rfl, 0, le_refl _, by simp at hv_eq; rw [hv_eq]; exact DerivesIn'.refl _⟩
    | cons x p' =>
      simp at hu_eq; obtain ⟨hx, _⟩ := hu_eq; exfalso
      have := h_target x (by rw [hv_eq]; simp)
      rw [← hx] at this; obtain ⟨t, ht⟩ := this; simp at ht
  | succ n' ih =>
    cases h with | step hprod hrest =>
    obtain ⟨r, hr_mem, hr_rew⟩ := hprod
    rw [ContextFreeRule.rewrites_iff] at hr_rew
    obtain ⟨p, q, hu_eq, hv_eq⟩ := hr_rew
    cases p with
    | nil =>
      simp at hu_eq; obtain ⟨hA, hq⟩ := hu_eq; subst hq; subst hA
      exact ⟨r, hr_mem, rfl, n' + 1, by omega, by simp at hv_eq; rw [hv_eq] at hrest; exact hrest⟩
    | cons x p' =>
      simp at hu_eq; obtain ⟨hx, hγ'⟩ := hu_eq
      have hrest' : DerivesIn' g (n' + 1)
          (Symbol.nonterminal A :: (p' ++ r.output ++ q)) target := by
        rw [hv_eq, ← hx] at hrest; simpa using hrest
      obtain ⟨r', hr'_mem, hr'_input, m, hm, hm_deriv⟩ :=
        ih A (p' ++ r.output ++ q) target hrest' h_target
      refine ⟨r', hr'_mem, hr'_input, m + 1, by omega, ?_⟩
      have hprod_γ' : g.Produces γ' (p' ++ r.output ++ q) := by
        rw [hγ']; refine ⟨r, hr_mem, ?_⟩
        convert ContextFreeRule.rewrites_of_exists_parts r p' q using 1; simp
      exact DerivesIn'.step (hprod_γ'.append_left r'.output) hm_deriv


/-- **Forward simulation.** If the sentential form `γ` derives the terminal string `w` in
`n` steps, then starting in state `loop` with `γ` (encoded on the stack above an arbitrary
suffix `extra`) and input `w`, the PDA can reach state `loop` having consumed all input
and exposed `extra` on top of the stack. -/
theorem toPDA_simulates :
    ∀ (n : ℕ) (γ : List (Symbol T g.NT)) (w : List T)
      (extra : List (Option (Symbol T g.NT))),
      DerivesIn' g n γ (w.map Symbol.terminal) →
      (toPDA g).Reaches (QState.loop, w, γ.map some ++ extra)
        (QState.loop, [], extra) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
    intro γ
    induction γ with
    | nil =>
      intro w extra h
      have ⟨_, hw⟩ := derivesIn'_nil_inv h
      cases w with
      | nil => simp; exact Relation.ReflTransGen.refl
      | cons _ _ => simp at hw
    | cons s γ' ih_γ =>
      intro w extra h
      match s with
      | Symbol.terminal t =>
        obtain ⟨w', hw_eq, hw'_deriv⟩ := derivesIn'_cons_terminal h
        match w with
        | [] => simp at hw_eq
        | t' :: w'' =>
          simp at hw_eq; obtain ⟨ht, hw'⟩ := hw_eq; subst ht
          rw [← hw'] at hw'_deriv
          simp only [List.map_cons]
          exact (toPDA_pop_terminal t' w'' (γ'.map some ++ extra)).trans
            (ih_γ w'' extra hw'_deriv)
      | Symbol.nonterminal A =>
        match n with
        | 0 =>
          exfalso; have := derivesIn'_zero_eq h
          cases w with | nil => simp at this | cons _ _ => simp at this
        | n' + 1 =>
          have h_target : ∀ s ∈ (w.map (Symbol.terminal (N := g.NT))),
              ∃ t, s = Symbol.terminal t := by simp
          obtain ⟨r, hr_mem, hr_input, m, hm, hm_deriv⟩ :=
            leftmost_step_n n' A γ' (w.map Symbol.terminal) h h_target
          simp only [List.map_cons]
          apply Relation.ReflTransGen.trans
          · subst hr_input
            exact toPDA_apply_rule r hr_mem w (γ'.map some ++ extra)
          · have : (r.output.map some ++ (List.map some γ' ++ extra)) =
                ((r.output ++ γ').map some ++ extra) := by
              simp [List.map_append]
            rw [this]
            exact ih_n m (by omega) (r.output ++ γ') w extra hm_deriv


/-- Prepending the same symbol to both sides preserves derivability:
if `γ ⇒* δ` then `s :: γ ⇒* s :: δ`. -/
lemma derives_cons_same (s : Symbol T g.NT) {γ δ : List (Symbol T g.NT)}
    (h : g.Derives γ δ) : g.Derives (s :: γ) (s :: δ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact ih.trans (Relation.ReflTransGen.single (hstep.append_left [s]))


set_option maxRecDepth 2048 in
/-- The `accept` state of the constructed PDA has no outgoing transitions:
no `Step` originates from a configuration whose state is `accept`. -/
lemma no_step_from_accept {w' : List T} {stk' : List (Option (Symbol T g.NT))} {cfg'}
    (h : (toPDA g).Step (QState.accept, w', stk') cfg') : False := by
  generalize hc : (QState.accept, w', stk') = c at h
  cases h with
  | mk q q' a pop push inp stk'' hmem =>
    simp only [Prod.mk.injEq] at hc
    obtain ⟨hq, _, _⟩ := hc; subst hq
    cases pop with
    | some _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
    | none => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem

/-- The `accept` state is a sink: any configuration reachable from `(accept, w', stk')`
is `(accept, w', stk')` itself. -/
lemma reaches_from_accept {w' : List T} {stk' : List (Option (Symbol T g.NT))} {cfg'}
    (h : (toPDA g).Reaches (QState.accept, w', stk') cfg') :
    cfg' = (QState.accept, w', stk') := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs no_step_from_accept


/-- `StepCount M n c₁ c₂` means the PDA `M` reaches configuration `c₂` from `c₁` in
exactly `n` steps. This is the step-counted refinement of `M.Reaches`. -/
inductive StepCount (M : PDA T σ γ₁) :
    ℕ → PDA.Config (α := T) (σ := σ) (γ := γ₁) →
    PDA.Config (α := T) (σ := σ) (γ := γ₁) → Prop where
  | refl (c) : StepCount M 0 c c
  | step {n c1 c2 c3} : M.Step c1 c2 → StepCount M n c2 c3 → StepCount M (n + 1) c1 c3

/-- A bounded `StepCount` derivation gives an unbounded `Reaches` derivation. -/
lemma StepCount.to_reaches {M : PDA T σ γ₁} {n c1 c2}
    (h : StepCount M n c1 c2) : M.Reaches c1 c2 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs ih

/-- Append a single step at the end of a `StepCount` sequence:
if `c₁ →ⁿ c₂` and `c₂ → c₃` then `c₁ →^{n+1} c₃`. -/
lemma StepCount.snoc {M : PDA T σ γ₁} {n : ℕ} {c1 c2 c3 : PDA.Config (α := T) (σ := σ) (γ := γ₁)}
    (h1 : StepCount M n c1 c2) (h2 : M.Step c2 c3) : StepCount M (n + 1) c1 c3 := by
  induction h1 with
  | refl => exact StepCount.step h2 (StepCount.refl _)
  | step hs _ ih => rw [Nat.add_right_comm]; exact StepCount.step hs (ih h2)

/-- Every `Reaches` derivation can be witnessed by an explicit `StepCount` of some length `n`. -/
lemma stepCount_of_reaches {M : PDA T σ γ₁} {c1 c2 : PDA.Config (α := T) (σ := σ) (γ := γ₁)}
    (h : M.Reaches c1 c2) : ∃ n, StepCount M n c1 c2 := by
  induction h with
  | refl => exact ⟨0, StepCount.refl _⟩
  | tail _ hs ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hn.snoc hs⟩


set_option maxRecDepth 2048 in
/-- Inversion lemma for a single PDA step: any transition out of `(q_src, w_src, stk_src)`
arises from some choice of next state `q'`, optional consumed input symbol `a`, optional
popped stack symbol `pop`, optional pushed stack symbol `push`, and tails `inp`, `stk`
of the input and stack respectively, with `(q', push) ∈ δ q_src a pop`. -/
lemma step_inv_aux
    {q_src : QState T g.NT} {w_src : List T}
    {stk_src : List (Option (Symbol T g.NT))} {cfg'}
    (h : (toPDA g).Step (q_src, w_src, stk_src) cfg')


    : ∃ (q' : QState T g.NT) (a : Option T)
        (pop push : Option (Option (Symbol T g.NT)))
        (inp : List T) (stk : List (Option (Symbol T g.NT))),
      w_src = a.toList ++ inp ∧
      stk_src = pop.toList ++ stk ∧
      cfg' = (q', inp, push.toList ++ stk) ∧
      (q', push) ∈ (toPDA g).step q_src a pop := by
  generalize hc : (q_src, w_src, stk_src) = c at h
  cases h with
  | mk q q' a pop push inp stk hmem =>
    simp only [Prod.mk.injEq] at hc
    obtain ⟨hq, hinp, hstk⟩ := hc; subst hq
    exact ⟨q', a, pop, push, inp, stk, hinp, hstk, rfl, hmem⟩


set_option maxRecDepth 2048 in
/-- Pushing a list `L` of length `|L|` consumes exactly `|L| + 1` steps (one push per symbol
plus one final transition from `pushing []` to `loop`). If a `StepCount` from `pushing L`
already takes at least `|L| + 1` steps, then after that prefix the PDA is in
`(loop, w_arg, L.reverse.map some ++ stk_arg)`, and the remaining `n - (|L|+1)` steps
reach the same target. -/
lemma pushing_stepCount_split
    (n : ℕ) {L : List (Symbol T g.NT)} {w_arg : List T}
    {stk_arg : List (Option (Symbol T g.NT))} {cfg'}
    (h : StepCount (toPDA g) n (QState.pushing L, w_arg, stk_arg) cfg')
    (hn : n ≥ L.length + 1) :
    StepCount (toPDA g) (n - (L.length + 1))
      (QState.loop, w_arg, L.reverse.map some ++ stk_arg) cfg' := by
  induction L generalizing n stk_arg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.map_nil, List.nil_append]
    cases h with
    | refl => omega
    | step hs hrest =>
      simp only [Nat.add_sub_cancel]
      obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
      cases pop with
      | some _ =>
        simp [Option.toList] at hs_stk
        obtain ⟨_, _⟩ := hs_stk
        cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
      | none =>
        simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
        cases a with
        | some _ => simp [toPDA] at hmem
        | none =>
          simp [toPDA] at hmem
          obtain ⟨hq', hpush⟩ := hmem; subst hq'
          cases push with
          | none => simp [Option.toList] at hcfg; rw [hcfg] at hrest; exact hrest
          | some _ => simp at hpush
  | cons s rest ih =>
    match n, h, hn with
    | 0, .refl _, hn => omega
    | n' + 1, .step hs hrest, hn =>
      obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
      cases pop with
      | some _ =>
        simp [Option.toList] at hs_stk
        obtain ⟨_, _⟩ := hs_stk
        cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
      | none =>
        simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
        cases a with
        | some _ => simp [toPDA] at hmem
        | none =>
          simp [toPDA] at hmem
          obtain ⟨hq', hpush⟩ := hmem; subst hq'
          cases push with
          | none => simp at hpush
          | some p =>
            simp at hpush; subst hpush
            simp [Option.toList] at hcfg
            rw [hcfg] at hrest
            have hnn : n' ≥ rest.length + 1 := by simp [List.length_cons] at hn; omega
            have := ih (n := n') (stk_arg := some s :: stk_arg) hrest hnn
            simp only [List.length_cons, List.reverse_cons, List.map_append,
              List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
            convert this using 1; omega


/-- Lower bound on the time to leave the `pushing` family of states. If fewer than
`|L| + 1` steps have been taken starting from `pushing L`, the PDA is still in some
`pushing L'` state. -/
lemma pushing_needs_steps
    (k : ℕ) {L : List (Symbol T g.NT)} {w_arg : List T}
    {stk_arg : List (Option (Symbol T g.NT))} {cfg'}
    (h : StepCount (toPDA g) k (QState.pushing L, w_arg, stk_arg) cfg')
    (hk : k < L.length + 1) :
    ∃ L', cfg'.1 = QState.pushing L' := by
  induction k generalizing L w_arg stk_arg with
  | zero => cases h with | refl => exact ⟨L, rfl⟩
  | succ k' ihk =>
    cases h with
    | step hs hrest =>
      cases L with
      | nil => simp at hk
      | cons s rest_L =>
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | some _ =>
          simp [Option.toList] at hs_stk
          obtain ⟨_, _⟩ := hs_stk
          cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | none =>
          simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
          cases a with
          | some _ => simp [toPDA] at hmem
          | none =>
            simp [toPDA] at hmem
            obtain ⟨hq', hpush⟩ := hmem; subst hq'
            cases push with
            | none => simp at hpush
            | some p =>
              simp at hpush; subst hpush
              simp [Option.toList] at hcfg
              rw [hcfg] at hrest
              exact ihk (L := rest_L) hrest (by simp at hk ⊢; omega)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
/-- **Backward simulation (loop-to-loop).** If from `(loop, w, γ.map some ++ [⊥])` the PDA
reaches `(loop, [], [⊥])` in exactly `n` steps (where `⊥ = none` is the bottom-of-stack
marker), then in the grammar `γ ⇒* w` (with `w` viewed as a sequence of terminals).

This is the core invariant for the converse direction: a successful run of the PDA from
`loop` back to `loop` while consuming `w` and shrinking the stack from `γ` to empty
corresponds to a derivation `γ ⇒* w`. -/
theorem backward_sim_n :
    ∀ (n : ℕ) (γ : List (Symbol T g.NT)) (w : List T),
    StepCount (toPDA g) n (QState.loop, w, γ.map some ++ [none])
      (QState.loop, [], [none]) →
    g.Derives γ (w.map Symbol.terminal) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro γ w h
    cases γ with
    | nil =>


      simp only [List.map_nil, List.nil_append] at h
      cases h with
      | refl => simp; exact Relation.ReflTransGen.refl
      | step hs hrest =>
        exfalso
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | none =>
          simp [Option.toList] at hs_stk; subst hs_stk
          cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem
        | some p =>
          simp [Option.toList] at hs_stk
          obtain ⟨hp, hstk_eq⟩ := hs_stk; subst hp; subst hstk_eq
          simp [Option.toList] at hw; subst hw
          cases a with
          | some _ => simp [toPDA] at hmem
          | none =>
            simp [toPDA] at hmem
            obtain ⟨hq', hpush⟩ := hmem; subst hq'
            cases push with
            | some _ => simp at hpush
            | none =>
              simp [Option.toList] at hcfg; rw [hcfg] at hrest
              have := hrest.to_reaches
              have := reaches_from_accept this
              simp [QState.loop, QState.accept] at this
    | cons sym γ' =>


      simp only [List.map_cons, List.cons_append] at h
      match n, h with
      | n' + 1, .step hs hrest =>
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | none =>
          simp [Option.toList] at hs_stk; subst hs_stk
          cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem
        | some p =>
          simp [Option.toList] at hs_stk
          obtain ⟨hp, hstk_eq⟩ := hs_stk; subst hp; subst hstk_eq

          cases sym with
          | terminal t =>

            simp [Option.toList] at hw
            cases a with
            | none => simp [toPDA] at hmem
            | some a_val =>
              simp [toPDA] at hmem
              obtain ⟨ha, hq', hpush⟩ := hmem; subst ha; subst hq'
              cases push with
              | some _ => simp at hpush
              | none =>
                simp [Option.toList] at hcfg hw
                rw [hcfg] at hrest; subst hw
                have ih_result := ih _ (by omega) γ' _ hrest
                simp only [List.map_cons]
                exact derives_cons_same (Symbol.terminal a_val) ih_result
          | nonterminal A =>

            simp [Option.toList] at hw
            cases a with
            | some _ => simp [toPDA] at hmem
            | none =>
              simp [toPDA] at hmem
              obtain ⟨r, hr_mem, hr_input, hq', hpush_eq⟩ := hmem
              subst hq'; subst hr_input
              cases push with
              | some _ => simp at hpush_eq
              | none =>
                simp [Option.toList] at hcfg hw; subst hw
                rw [hcfg] at hrest


                by_cases hn1 : n' ≥ r.output.reverse.length + 1
                · have hsplit := pushing_stepCount_split n'
                    (L := r.output.reverse) (w_arg := w)
                    (stk_arg := γ'.map some ++ [none])
                    (cfg' := (QState.loop, [], [none]))
                    hrest hn1
                  simp only [List.reverse_reverse] at hsplit
                  have hmap : r.output.map some ++ (γ'.map some ++ [none]) =
                      (r.output ++ γ').map some ++ [none] := by simp [List.map_append]
                  rw [hmap] at hsplit
                  have ih_result := ih _ (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl (n' + 1))) (r.output ++ γ') w hsplit
                  have hprod : g.Produces (Symbol.nonterminal r.input :: γ') (r.output ++ γ') :=
                    ⟨r, hr_mem, ContextFreeRule.Rewrites.head γ'⟩
                  exact hprod.single.trans ih_result
                · exfalso; push_neg at hn1
                  have := pushing_needs_steps n'
                    (L := r.output.reverse) (w_arg := w)
                    (stk_arg := γ'.map some ++ [none])
                    (cfg' := (QState.loop, [], [none]))
                    hrest (by simp [List.length_reverse] at hn1 ⊢; exact hn1)
                  obtain ⟨L', hL'⟩ := this
                  simp at hL'

end CFGtoPDA

namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}
variable {g : ContextFreeGrammar T}


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- **Stack-shape invariant for one step.** As long as the PDA is not transitioning into
or out of the special `start` / `accept` states, a stack of the form `L.map some ++ [none]`
(a list of grammar symbols on top of the bottom marker) is preserved as `L'.map some ++ [none]`
after one step, for some new list `L'`. -/
lemma stack_invariant_step
    {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
    (hs : (toPDA g).Step c1 c2)
    {L : List (Symbol T g.NT)}
    (hstk : c1.2.2 = L.map some ++ [none])
    (hna1 : c1.1 ≠ QState.accept)
    (hna2 : c2.1 ≠ QState.accept)
    (hns1 : c1.1 ≠ QState.start) :
    ∃ L' : List (Symbol T g.NT), c2.2.2 = L'.map some ++ [none] := by
  generalize hc : c1 = cc at hs
  cases hs with
  | mk q q' a pop push inp stk hmem =>
    subst hc
    simp only [Prod.fst, Prod.snd] at hna1 hna2 hns1 hstk ⊢

    cases pop with
    | none =>
      simp [Option.toList] at hstk

      cases push with
      | none => exact ⟨L, by simp [Option.toList, hstk]⟩
      | some pv =>
        simp [Option.toList]


        cases q with
        | start => exact absurd rfl hns1
        | loop => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | pushing Lp =>
          cases Lp with
          | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | cons sp rp =>
            cases a with
            | some _ => simp [toPDA] at hmem
            | none =>
              simp [toPDA] at hmem
              obtain ⟨_, hpv⟩ := hmem; subst hpv
              exact ⟨sp :: L, by simp [hstk, List.map_cons, List.cons_append]⟩
        | accept => exact absurd rfl hna1
    | some p =>
      simp [Option.toList] at hstk

      cases L with
      | nil =>
        simp at hstk; obtain ⟨hp, hs⟩ := hstk; subst hp; subst hs

        cases q with
        | loop => cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem; obtain ⟨hq', _⟩ := hmem; subst hq'; exact absurd rfl hna2
        | start => exact absurd rfl hns1
        | pushing Lp => cases Lp with
          | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | cons _ _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | accept => exact absurd rfl hna1
      | cons sL L' =>
        simp at hstk; obtain ⟨hp, hs⟩ := hstk; subst hp
        cases push with
        | none => exact ⟨L', by simp [Option.toList, hs]⟩
        | some pv =>
          simp [Option.toList]


          cases q with
          | loop =>
            cases sL with
            | terminal t => cases a with
              | none => simp [toPDA] at hmem
              | some _ => simp [toPDA] at hmem
            | nonterminal B => cases a with
              | some _ => simp [toPDA] at hmem
              | none => simp [toPDA] at hmem
          | start => exact absurd rfl hns1
          | pushing Lp => cases Lp with
            | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
            | cons _ _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | accept => exact absurd rfl hna1


set_option maxRecDepth 2048 in
/-- No transition in the constructed PDA targets the `start` state:
once the PDA has left `start`, it never returns. -/
lemma no_target_start {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
    (h : (toPDA g).Step c1 c2) : c2.1 ≠ QState.start := by
  generalize hc : c1 = cc at h
  cases h with
  | mk q q' a pop push inp stk hmem =>
    subst hc; simp only [Prod.fst]

    cases q with
    | start => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
                (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.pushing])
    | accept => cases pop <;> cases a <;> simp [toPDA] at hmem
    | loop =>
      cases pop with
      | none => cases a <;> simp [toPDA] at hmem
      | some val =>
        cases val with
        | none => cases a <;> simp [toPDA] at hmem <;>
                  (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.accept])
        | some sym =>
          cases sym with
          | terminal t => cases a <;> simp [toPDA] at hmem <;>
                          (obtain ⟨_, hq, _⟩ := hmem; simp [hq, QState.start, QState.loop])
          | nonterminal A => cases a <;> simp [toPDA] at hmem <;>
                            (obtain ⟨_, _, _, hp⟩ := hmem; simp [hp.1, QState.start, QState.pushing])
    | pushing Lp =>
      cases Lp with
      | nil => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
               (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.loop])
      | cons s rest => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
                       (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.pushing])


/-- Reachable-version of `stack_invariant_step`: along any run between two non-accept
configurations (where the start configuration is also not `start`), the stack shape
`L.map some ++ [⊥]` is preserved, possibly with a different list `L'`. -/
lemma stack_invariant_reaches
    {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
    (h : (toPDA g).Reaches c1 c2)
    {L : List (Symbol T g.NT)}
    (hstk : c1.2.2 = L.map some ++ [none])
    (hna1 : c1.1 ≠ QState.accept)
    (hna2 : c2.1 ≠ QState.accept)
    (hns1 : c1.1 ≠ QState.start) :
    ∃ L' : List (Symbol T g.NT), c2.2.2 = L'.map some ++ [none] := by
  induction h with
  | refl => exact ⟨L, hstk⟩
  | @tail a_cfg b_cfg hs_prefix hs_last ih_step =>

    by_cases ha_acc : a_cfg.1 = QState.accept
    ·
      obtain ⟨q_a, w_a, stk_a⟩ := a_cfg; simp at ha_acc; subst ha_acc
      exact absurd hs_last no_step_from_accept
    · obtain ⟨L', hL'⟩ := ih_step ha_acc

      have hns_a : a_cfg.1 ≠ QState.start := by
        intro heq
        cases Relation.ReflTransGen.cases_tail hs_prefix with
        | inl h_eq => rw [h_eq] at heq; exact hns1 heq
        | inr h_ex =>
          obtain ⟨mid, _, hmid_step⟩ := h_ex
          exact no_target_start hmid_step heq
      exact stack_invariant_step hs_last hL' ha_acc hna2 hns_a


set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- **Backward direction, auxiliary form.** Any accepting run of the constructed PDA on `w`
— starting in `(start, w, [])` and ending in `(accept, [], stk)` for some final stack `stk`
— yields a CFG derivation `[S] ⇒* w` from the start variable `S = g.initial`. -/
theorem toPDA_language_backward_aux
    {T : Type u_pda} (g : ContextFreeGrammar T) (w : List T)
    (stk : List (Option (Symbol T g.NT))) :
    (CFGtoPDA.toPDA g).Reaches (CFGtoPDA.QState.start, w, [])
      (CFGtoPDA.QState.accept, [], stk) →
    g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
  intro hreach


  cases Relation.ReflTransGen.cases_head hreach with
  | inl heq => simp [QState.start, QState.accept] at heq
  | inr hex =>
    obtain ⟨mid1, hstep1, hrest1⟩ := hex

    obtain ⟨q1', a1, pop1, push1, inp1, stk1, hw1, hs1, hcfg1, hmem1⟩ := step_inv_aux hstep1
    cases pop1 with
    | some _ => simp [Option.toList] at hs1
    | none =>
      simp [Option.toList] at hs1 hw1; subst hs1; subst hw1
      cases a1 with
      | some _ => simp [toPDA] at hmem1
      | none =>
        simp [toPDA] at hmem1
        obtain ⟨hq1', hpush1⟩ := hmem1; subst hq1'
        cases push1 with
        | none => simp at hpush1
        | some p1 =>
          simp at hpush1; subst hpush1
          simp [Option.toList] at hcfg1
          rw [hcfg1] at hrest1


          cases Relation.ReflTransGen.cases_tail hrest1 with
          | inl heq => simp [QState.pushing, QState.accept] at heq
          | inr hex2 =>
            obtain ⟨mid2, hrest2, hstep2⟩ := hex2


            generalize hc_acc : (QState.accept, ([] : List T), stk) = cfg_acc at hstep2
            cases hstep2 with
            | mk q2 q2' a2 pop2 push2 inp2 stk2 hmem2 =>
              simp only [Prod.mk.injEq] at hc_acc
              obtain ⟨hq2_acc, hinp2, hstk2_eq⟩ := hc_acc; subst hq2_acc

              cases pop2 with
              | none =>
                simp [Option.toList] at *
                cases q2 with
                | start => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.pushing] at h1)
                | accept => cases a2 <;> simp [toPDA] at hmem2
                | loop => cases a2 <;> simp [toPDA] at hmem2
                | pushing Lp =>
                  cases Lp with
                  | nil => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop] at h1)
                  | cons _ _ => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.pushing] at h1)
              | some p2 =>
                simp [Option.toList] at *
                cases q2 with
                | start => cases a2 <;> simp [toPDA] at hmem2
                | accept => cases a2 <;> simp [toPDA] at hmem2
                | pushing Lp2 =>
                  cases Lp2 with
                  | nil => cases a2 <;> simp [toPDA] at hmem2 <;>
                    (try obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop, QState.pushing] at h1)
                  | cons _ _ => cases a2 <;> simp [toPDA] at hmem2 <;>
                    (try obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop, QState.pushing] at h1)
                | loop =>
                  cases p2 with
                  | some ss2 =>
                    cases ss2 with
                    | terminal t2 => cases a2 with
                      | none => simp [toPDA] at hmem2
                      | some _ => simp [toPDA] at hmem2
                    | nonterminal B2 => cases a2 with
                      | some _ => simp [toPDA] at hmem2
                      | none => simp [toPDA] at hmem2
                  | none =>

                    cases a2 with
                    | some _ => simp [toPDA] at hmem2
                    | none =>
                      simp [toPDA] at hmem2
                      subst hmem2
                      simp [Option.toList] at hinp2 hstk2_eq hrest2
                      subst hinp2; subst hstk2_eq


                      have hgood := stack_invariant_reaches hrest2
                        (L := []) (by simp)
                        (by simp [QState.pushing, QState.accept])
                        (by simp [QState.loop, QState.accept])
                        (by simp [QState.pushing, QState.start])
                      obtain ⟨L', hL'⟩ := hgood
                      simp at hL'
                      cases L' with
                      | nil =>
                        simp at hL'; subst hL'
                        obtain ⟨m, hm⟩ := stepCount_of_reaches hrest2
                        have hm_ge : m ≥ 2 := by


                          by_contra hlt; push_neg at hlt
                          have := pushing_needs_steps m (L := [Symbol.nonterminal g.initial])
                            (w_arg := inp1) (stk_arg := [none]) (cfg' := (QState.loop, [], [none]))
                            hm (by simpa using hlt)
                          obtain ⟨L', hL''⟩ := this
                          simp at hL''
                        have hsplit := pushing_stepCount_split m
                          (L := [Symbol.nonterminal g.initial]) (w_arg := inp1)
                          (stk_arg := [none])
                          (cfg' := (QState.loop, [], [none]))
                          hm hm_ge
                        simp only [List.length_cons, List.length_nil, List.reverse_cons,
                          List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
                          List.singleton_append] at hsplit
                        exact backward_sim_n (m - 2) [Symbol.nonterminal g.initial] inp1 hsplit
                      | cons _ _ => simp at hL'

/-- **Backward direction.** If the PDA `toPDA g` accepts `w`, then `g` derives `w` from
its start variable, i.e. `w ∈ L(g)`. -/
theorem toPDA_language_backward
    (g : ContextFreeGrammar T) (w : List T) :
    (toPDA g).Accepts w →
    g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
  intro ⟨q, hq, stk, hreach⟩
  simp [toPDA] at hq; subst hq
  exact toPDA_language_backward_aux g w stk hreach

set_option maxRecDepth 2048 in
/-- **Correctness of the CFG → PDA construction.** The PDA produced by `toPDA g`
recognizes exactly the language of `g`: `L(toPDA g) = L(g)`. -/
theorem toPDA_language (g : ContextFreeGrammar T) :
    (CFGtoPDA.toPDA g).language = g.language := by
  ext w
  simp only [PDA.language, PDA.Accepts, ContextFreeGrammar.mem_language_iff]
  constructor
  · exact toPDA_language_backward g w
  · intro hderiv
    obtain ⟨n, hn⟩ := derives_to_derivesIn' hderiv
    refine ⟨QState.accept, Set.mem_singleton _, [], ?_⟩
    apply Relation.ReflTransGen.head
    · have h := PDA.Step.mk (M := toPDA g) QState.start
        (QState.pushing [Symbol.nonterminal g.initial])
        (none : Option T) (none : Option (Option (Symbol T g.NT)))
        (some none) w [] (by simp [toPDA])
      simpa [Option.toList] using h
    apply Relation.ReflTransGen.trans
    · exact toPDA_push_list [Symbol.nonterminal g.initial] w [none]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.singleton_append]
    apply Relation.ReflTransGen.trans
    · have := @toPDA_simulates T g n [Symbol.nonterminal g.initial] w [none] hn
      simpa [List.map] using this
    apply Relation.ReflTransGen.single
    · have h := PDA.Step.mk (M := toPDA g) QState.loop QState.accept
        (none : Option T) (some (none : Option (Symbol T g.NT))) none [] []
        (by simp [toPDA])
      simpa [Option.toList] using h

/-- **Theorem (Converting CFGs to PDAs), Sipser Lecture 4.**
If `A` is a context-free language, then some pushdown automaton recognizes `A`. -/
theorem cfg_to_pda {A : Language T} (h : ContextFree.IsContextFree A) :
    IsPDARecognizable A := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨_, _, toPDA g, toPDA_language g⟩

end CFGtoPDA
