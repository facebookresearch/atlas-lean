/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
import Std.Do.Triple.Basic
open Std.Do
open scoped Std.Do
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Native state contracts pilot

Teaching example for checked debits over native
`EStateM`. Clause map: C1 balances in `debit`;
C2 `debit` def; C3 `debit2` def; C4 `triple_debit`
and `triple_debit2` via `Triple.bind`; C5
`run_debit` and `run_debit2` via `of_wp_run_eq`;
C6 `fixOne`, `fixTwo` and `#eval`; C7 mutants
`debitStrict`, `debitClear`, `debit2Rollback`;
C8 `debitEST2` and `debitST2`; C9 `triple_weak`.

Producer: Muse Code, profile
`meta/muse-spark-1.3-internal` rev 3.
-/
/-- Checked debit: success iff `a ≤ b`. C1, C2. -/
def debit (a : Nat) : EStateM Unit Nat Unit :=
  EStateM.bind EStateM.get fun b =>
    if a ≤ b then EStateM.set (b - a)
    else EStateM.throw ()
/-- Sequenced debits, no rollback. C3. -/
def debit2 (a c : Nat) : EStateM Unit Nat Unit :=
  debit a >>= fun _ => debit c
#print axioms debit
#print axioms debit2
/-- One-debit spec with precise posts. C4. -/
theorem triple_debit (a b : Nat) :
    Triple (debit a) (spred(fun s => ⌜s = b⌝))
      post⟨fun (_ : Unit) s' => ⌜a ≤ b ∧ s' = b - a⌝,
        fun (_ : Unit) s' => ⌜b < a ∧ s' = b⌝⟩ := by
  apply Triple.iff.mpr
  intro s hs
  simp at hs
  subst hs
  simp only [wp, PredTrans.apply, debit,
    EStateM.run, EStateM.bind, EStateM.get]
  by_cases h : a ≤ s
  · simp only [ite_eq_left h] at *
    exact ⟨h, rfl⟩
  · simp only [ite_eq_right h] at *
    have hlt : s < a := by omega
    exact ⟨hlt, rfl⟩
#print axioms triple_debit
/-- First debit to mid assertion. C4, helper. -/
private theorem triple_first (a c b : Nat) :
    Triple (debit a) (spred(fun s => ⌜s = b⌝))
      post⟨fun (_ : Unit) s1 => ⌜a ≤ b ∧ s1 = b - a⌝,
        fun (_ : Unit) s' => ⌜(b < a ∧ s' = b) ∨
          (a ≤ b ∧ b - a < c ∧ s' = b - a)⌝⟩ := by
  apply Triple.iff.mpr
  intro s hs
  simp at hs
  subst hs
  simp only [wp, PredTrans.apply, debit,
    EStateM.run, EStateM.bind, EStateM.get]
  by_cases h : a ≤ s
  · simp only [ite_eq_left h] at *
    exact ⟨h, rfl⟩
  · simp only [ite_eq_right h] at *
    have hlt : s < a := by omega
    exact Or.inl ⟨hlt, rfl⟩
#print axioms triple_first
/-- Second debit from mid assertion. C4, helper. -/
private theorem triple_second (a c b : Nat) (_u : Unit) :
    Triple (debit c)
      (spred(fun s1 => ⌜a ≤ b ∧ s1 = b - a⌝))
      post⟨fun (_ : Unit) s' => ⌜a ≤ b ∧ c ≤ b - a ∧
          s' = b - a - c⌝,
        fun (_ : Unit) s' => ⌜(b < a ∧ s' = b) ∨
          (a ≤ b ∧ b - a < c ∧ s' = b - a)⌝⟩ := by
  apply Triple.iff.mpr
  intro s1 hs1
  simp at hs1
  obtain ⟨hab, heq⟩ := hs1
  subst heq
  simp only [wp, PredTrans.apply, debit,
    EStateM.run, EStateM.bind, EStateM.get]
  by_cases h : c ≤ b - a
  · simp only [ite_eq_left h] at *
    exact ⟨hab, h, rfl⟩
  · simp only [ite_eq_right h] at *
    have hlt : b - a < c := by omega
    exact Or.inr ⟨hab, hlt, rfl⟩
#print axioms triple_second
/-- Two-debit spec via `Triple.bind`. C3, C4. -/
theorem triple_debit2 (a c b : Nat) :
    Triple (debit2 a c) (spred(fun s => ⌜s = b⌝))
      post⟨fun (_ : Unit) s' => ⌜a ≤ b ∧ c ≤ b - a ∧
          s' = b - a - c⌝,
        fun (_ : Unit) s' => ⌜(b < a ∧ s' = b) ∨
          (a ≤ b ∧ b - a < c ∧ s' = b - a)⌝⟩ := by
  simp only [debit2]
  exact Triple.bind _ _ (triple_first a c b)
    (fun u => triple_second a c b u)
#print axioms triple_debit2
/-- Run predicate for one debit. C5. -/
private def pred1 (a b : Nat)
    (r : EStateM.Result Unit Nat Unit) : Prop :=
  (a ≤ b ∧ r = EStateM.Result.ok () (b - a)) ∨
    (b < a ∧ r = EStateM.Result.error () b)
#print axioms pred1
/-- One-debit run via `of_wp_run_eq`. C5. -/
theorem run_debit (a b : Nat) :
    pred1 a b ((debit a).run b) := by
  have hT := triple_debit a b
  have hQ :
      (post⟨fun (_ : Unit) s' => ⌜a ≤ b ∧ s' = b - a⌝,
        fun (_ : Unit) s' => ⌜b < a ∧ s' = b⌝⟩ :
        PostCond Unit (.except Unit (.arg Nat .pure))) ⊢ₚ
      post⟨fun (u : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.error e s')⌝⟩ := by
    refine PostCond.entails.mk ?_ ?_
    · intro u s hs
      simp at hs
      obtain ⟨hab, heq⟩ := hs
      subst heq
      cases u
      show pred1 a b (EStateM.Result.ok () (b - a))
      exact Or.inl ⟨hab, rfl⟩
    · constructor
      · intro e s hs
        simp at hs
        obtain ⟨hlt, heq⟩ := hs
        cases e
        show pred1 a b (EStateM.Result.error () s)
        have heq2 :
            (EStateM.Result.error () s :
              EStateM.Result Unit Nat Unit) =
            EStateM.Result.error () b := by rw [heq]
        exact Or.inr ⟨hlt, heq2⟩
      · trivial
  have hWP :
      (spred(fun s => ⌜s = b⌝) :
        Assertion (.except Unit (.arg Nat .pure))) ⊢ₛ
      wp⟦debit a⟧ post⟨fun (u : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.error e s')⌝⟩ :=
    SPred.entails.trans (Triple.iff.mp hT)
      ((wp (debit a)).mono _ _ hQ)
  have hat :
      ⊢ₛ wp⟦debit a⟧ post⟨fun (u : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred1 a b (EStateM.Result.error e s')⌝⟩ b :=
    fun _ => hWP b rfl
  exact EStateM.of_wp_run_eq rfl (pred1 a b) hat
#print axioms run_debit
/-- Run predicate for two debits. C5. -/
private def pred2 (a c b : Nat)
    (r : EStateM.Result Unit Nat Unit) : Prop :=
  (a ≤ b ∧ c ≤ b - a ∧
    r = EStateM.Result.ok () (b - a - c)) ∨
    (b < a ∧ r = EStateM.Result.error () b) ∨
    (a ≤ b ∧ b - a < c ∧
      r = EStateM.Result.error () (b - a))
#print axioms pred2
/-- Two-debit run via `of_wp_run_eq`. C5. -/
theorem run_debit2 (a c b : Nat) :
    pred2 a c b ((debit2 a c).run b) := by
  have hT := triple_debit2 a c b
  have hQ :
      (post⟨fun (_ : Unit) s' =>
          ⌜a ≤ b ∧ c ≤ b - a ∧ s' = b - a - c⌝,
        fun (_ : Unit) s' => ⌜(b < a ∧ s' = b) ∨
          (a ≤ b ∧ b - a < c ∧ s' = b - a)⌝⟩ :
        PostCond Unit (.except Unit (.arg Nat .pure))) ⊢ₚ
      post⟨fun (u : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.error e s')⌝⟩ := by
    refine PostCond.entails.mk ?_ ?_
    · intro u s hs
      simp at hs
      obtain ⟨hab, hc, heq⟩ := hs
      subst heq
      cases u
      show pred2 a c b
        (EStateM.Result.ok () (b - a - c))
      exact Or.inl ⟨hab, hc, rfl⟩
    · constructor
      · intro e s hs
        simp at hs
        cases hs with
        | inl h =>
          obtain ⟨hlt, heq⟩ := h
          cases e
          show pred2 a c b
            (EStateM.Result.error () s)
          have heq2 :
              (EStateM.Result.error () s :
                EStateM.Result Unit Nat Unit) =
              EStateM.Result.error () b := by rw [heq]
          exact Or.inr (Or.inl ⟨hlt, heq2⟩)
        | inr h =>
          obtain ⟨hab, hlt, heq⟩ := h
          cases e
          show pred2 a c b
            (EStateM.Result.error () s)
          have heq2 :
              (EStateM.Result.error () s :
                EStateM.Result Unit Nat Unit) =
              EStateM.Result.error () (b - a) := by
            rw [heq]
          exact Or.inr (Or.inr ⟨hab, hlt, heq2⟩)
      · trivial
  have hWP :
      (spred(fun s => ⌜s = b⌝) :
        Assertion (.except Unit (.arg Nat .pure))) ⊢ₛ
      wp⟦debit2 a c⟧ post⟨fun (u : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.error e s')⌝⟩ :=
    SPred.entails.trans (Triple.iff.mp hT)
      ((wp (debit2 a c)).mono _ _ hQ)
  have hat :
      ⊢ₛ wp⟦debit2 a c⟧ post⟨fun (u : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.ok u s')⌝,
        fun (e : Unit) s' =>
        ⌜pred2 a c b (EStateM.Result.error e s')⌝⟩ b :=
    fun _ => hWP b rfl
  exact EStateM.of_wp_run_eq rfl (pred2 a c b) hat
#print axioms run_debit2
/-- Success equality from `run_debit`. C5. -/
theorem run_ok (a b : Nat) (h : a ≤ b) :
    (debit a).run b =
      EStateM.Result.ok () (b - a) := by
  have hr := run_debit a b
  simp only [pred1] at hr
  cases hr with
  | inl h2 => exact h2.2
  | inr h2 =>
    have hlt := h2.1
    have hf : False := by omega
    exact False.elim hf
#print axioms run_ok
/-- Failure equality from `run_debit`. C5. -/
theorem run_err (a b : Nat) (h : b < a) :
    (debit a).run b =
      EStateM.Result.error () b := by
  have hr := run_debit a b
  simp only [pred1] at hr
  cases hr with
  | inl h2 =>
    have hab := h2.1
    have hf : False := by omega
    exact False.elim hf
  | inr h2 => exact h2.2
#print axioms run_err
/-- Two-debit success equality. C5. -/
theorem run2_ok (a c b : Nat) (h1 : a ≤ b)
    (h2 : c ≤ b - a) :
    (debit2 a c).run b =
      EStateM.Result.ok () (b - a - c) := by
  have hr := run_debit2 a c b
  simp only [pred2] at hr
  cases hr with
  | inl h => exact h.2.2
  | inr h =>
    cases h with
    | inl h3 =>
      have hf : False := by omega
      exact False.elim hf
    | inr h3 =>
      have hf : False := by omega
      exact False.elim hf
#print axioms run2_ok
/-- Two-debit first-failure equality. C5. -/
theorem run2_fail1 (a c b : Nat) (h : b < a) :
    (debit2 a c).run b =
      EStateM.Result.error () b := by
  have hr := run_debit2 a c b
  simp only [pred2] at hr
  cases hr with
  | inl h2 =>
    have hf : False := by omega
    exact False.elim hf
  | inr h2 =>
    cases h2 with
    | inl h3 => exact h3.2
    | inr h3 =>
      have hf : False := by omega
      exact False.elim hf
#print axioms run2_fail1
/-- Two-debit second-failure equality. C5. -/
theorem run2_fail2 (a c b : Nat) (h1 : a ≤ b)
    (h2 : b - a < c) :
    (debit2 a c).run b =
      EStateM.Result.error () (b - a) := by
  have hr := run_debit2 a c b
  simp only [pred2] at hr
  cases hr with
  | inl h =>
    have hf : False := by omega
    exact False.elim hf
  | inr h =>
    cases h with
    | inl h3 =>
      have hf : False := by omega
      exact False.elim hf
    | inr h3 => exact h3.2.2
#print axioms run2_fail2
/-- Strict-guard mutant, fails at equality. C7. -/
private def debitStrict (a : Nat) :
    EStateM Unit Nat Unit :=
  EStateM.bind EStateM.get fun b =>
    if a < b then EStateM.set (b - a)
    else EStateM.throw ()
#print axioms debitStrict
/-- Clear-on-error mutant, zeroes state. C7. -/
private def debitClear (a : Nat) :
    EStateM Unit Nat Unit :=
  EStateM.bind EStateM.get fun b =>
    if a ≤ b then EStateM.set (b - a)
    else EStateM.bind (EStateM.set 0)
      fun _ => EStateM.throw ()
#print axioms debitClear
/-- Whole-pair rollback mutant. C7. -/
private def debit2Rollback (a c : Nat) :
    EStateM Unit Nat Unit :=
  EStateM.bind EStateM.get fun b0 =>
    EStateM.bind (debit a) fun _ =>
      EStateM.tryCatch (debit c) fun _ =>
        EStateM.bind (EStateM.set b0)
          fun _ => EStateM.throw ()
#print axioms debit2Rollback
/-- Debit over `ExceptT` on `StateM`. C8. -/
private def debitEST (a : Nat) :
    ExceptT Unit (StateM Nat) Unit := do
  let b ← MonadStateOf.get (m := ExceptT Unit (StateM Nat))
  if a ≤ b then
    MonadStateOf.set (m := ExceptT Unit (StateM Nat)) (b - a)
  else throw ()
#print axioms debitEST
/-- Sequenced `ExceptT` debits. C8. -/
private def debitEST2 (a c : Nat) :
    ExceptT Unit (StateM Nat) Unit :=
  debitEST a >>= fun _ => debitEST c
#print axioms debitEST2
/-- Debit over `StateT` on `Except`. C8. -/
private def debitST (a : Nat) :
    StateT Nat (Except Unit) Unit := do
  let b ← MonadStateOf.get (m := StateT Nat (Except Unit))
  if a ≤ b then
    MonadStateOf.set (m := StateT Nat (Except Unit)) (b - a)
  else throw ()
#print axioms debitST
/-- Sequenced `StateT` debits. C8. -/
private def debitST2 (a c : Nat) :
    StateT Nat (Except Unit) Unit :=
  debitST a >>= fun _ => debitST c
#print axioms debitST2
/-- Result equality for fixtures. C6. -/
private def beqRes (r1 r2 :
    EStateM.Result Unit Nat Unit) : Bool :=
  match r1, r2 with
  | .ok () s1, .ok () s2 => s1 == s2
  | .error () s1, .error () s2 => s1 == s2
  | _, _ => false
#print axioms beqRes
/-- One-debit fixture, same for base/mutants. C6, C7. -/
private def fixOne
    (impl : Nat -> EStateM Unit Nat Unit) : Bool :=
  beqRes ((impl 5).run 5)
    (EStateM.Result.ok () 0) &&
  beqRes ((impl 0).run 5)
    (EStateM.Result.ok () 5) &&
  beqRes ((impl 6).run 5)
    (EStateM.Result.error () 5) &&
  beqRes ((impl 3).run 10)
    (EStateM.Result.ok () 7) &&
  beqRes ((impl 0).run 0)
    (EStateM.Result.ok () 0)
#print axioms fixOne
/-- Two-debit fixture, same for base/mutants. C6, C7. -/
private def fixTwo
    (impl : Nat -> Nat -> EStateM Unit Nat Unit) :
    Bool :=
  beqRes ((impl 3 7).run 10)
    (EStateM.Result.ok () 0) &&
  beqRes ((impl 6 0).run 5)
    (EStateM.Result.error () 5) &&
  beqRes ((impl 3 4).run 5)
    (EStateM.Result.error () 2) &&
  beqRes ((impl 0 1).run 0)
    (EStateM.Result.error () 0)
#print axioms fixTwo
/-- `ExceptT` observation is error plus `2`. C8. -/
private def checkEST : Bool :=
  match ((debitEST2 3 4).run).run 5 with
  | (Except.error (), 2) => true
  | _ => false
#print axioms checkEST
/-- `StateT` observation is error alone. C8. -/
private def checkST : Bool :=
  match (debitST2 3 4).run 5 with
  | Except.error () => true
  | _ => false
#print axioms checkST
/-- Failing assertion harness, IO only here. C6-C8. -/
private def runChecks : IO Unit := do
  let c1 := fixOne debit
  let m1 := fixOne debitStrict
  let m2 := fixOne debitClear
  let c2 := fixTwo debit2
  let m3 := fixTwo debit2Rollback
  let t1 := checkEST
  let t2 := checkST
  IO.println s!"fixOne base: {c1} (want true)"
  IO.println s!"fixOne strict: {m1} (want false)"
  IO.println s!"fixOne clear: {m2} (want false)"
  IO.println s!"fixTwo base: {c2} (want true)"
  IO.println s!"fixTwo roll: {m3} (want false)"
  IO.println s!"estObs: {t1} (want true)"
  IO.println s!"stObs: {t2} (want true)"
  if c1 && !m1 && !m2 && c2 && !m3 && t1 && t2 then
    IO.println "ALL CHECKS PASS"
  else throw (IO.userError "CHECK FAILURE")
#print axioms runChecks
#eval runChecks
-- C6 concrete runs via kernel evaluation.
example : (debit 5).run 5 =
  EStateM.Result.ok () 0 := rfl
example : (debit 0).run 5 =
  EStateM.Result.ok () 5 := rfl
example : (debit 6).run 5 =
  EStateM.Result.error () 5 := rfl
example : (debit2 3 7).run 10 =
  EStateM.Result.ok () 0 := rfl
example : (debit2 6 0).run 5 =
  EStateM.Result.error () 5 := rfl
example : (debit2 3 4).run 5 =
  EStateM.Result.error () 2 := rfl
example : (debit2 0 1).run 0 =
  EStateM.Result.error () 0 := rfl
-- C6 via C5 equalities, bound to those sigs.
example : (debit 5).run 5 =
  EStateM.Result.ok () 0 := run_ok 5 5 (by omega)
example : (debit 6).run 5 =
  EStateM.Result.error () 5 := run_err 6 5 (by omega)
example : (debit2 3 7).run 10 =
  EStateM.Result.ok () 0 := run2_ok 3 7 10 (by omega)
  (by omega)
example : (debit2 6 0).run 5 =
  EStateM.Result.error () 5 := run2_fail1 6 0 5 (by omega)
example : (debit2 3 4).run 5 =
  EStateM.Result.error () 2 := run2_fail2 3 4 5 (by omega)
  (by omega)
-- C6 instantiations of universal specs.
example := triple_debit 5 5
example := triple_debit2 3 7 10
example := run_debit 5 5
example := run_debit2 3 7 10
-- C8 transformer runs via kernel.
example : ((debitEST2 3 4).run).run 5 =
  (Except.error (), 2) := rfl
example : (debitST2 3 4).run 5 =
  Except.error () := rfl
-- C7 mutant behaviours, documented only.
example : (debitStrict 5).run 5 =
  EStateM.Result.error () 5 := rfl
example : (debitClear 6).run 5 =
  EStateM.Result.error () 0 := rfl
example : (debit2Rollback 3 4).run 5 =
  EStateM.Result.error () 5 := rfl
-- Weak True error post holds even on failure, so
-- it cannot prove absence of errors. Precise
-- C4-C5 posts are still required. C9.
private theorem triple_weak :
    Triple (debit 6) (spred(fun s => ⌜s = 5⌝))
      post⟨fun (_ : Unit) s' => ⌜6 ≤ 5 ∧ s' = 5 - 6⌝,
        fun (_ : Unit) _ => ⌜True⌝⟩ := by
  apply Triple.iff.mpr
  intro s hs
  simp at hs
  subst hs
  simp only [wp, PredTrans.apply, debit,
    EStateM.run, EStateM.bind, EStateM.get]
  have h : ¬ 6 ≤ (5 : Nat) := by omega
  simp only [ite_eq_right h] at *
  trivial
#print axioms triple_weak
