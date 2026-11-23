/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.IMP.Hoare
import CSLibExt.Languages.IMP.HoareTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtlasTeaching.IMPInvariants

open Cslib.IMP

def loopGuard (x : Nat) : BExp :=
  .not (.eq (.var x) (.const 0))

def loopBody (x y : Nat) : Cmd :=
  .seq (.assign y (.add (.var y) (.const 1))) (.assign x (.sub (.var x) (.const 1)))

def transfer (x y : Nat) : Cmd :=
  .while (loopGuard x) (loopBody x y)

def transferPre (x y n : Nat) : Assertion :=
  fun s => s x = n ∧ s y = 0

def transferInv (x y n : Nat) : Assertion :=
  fun s => s x + s y = n

def transferVariant (x : Nat) : State → Nat :=
  fun s => s x

def transferPost (x y n : Nat) : Assertion :=
  fun s => s x = 0 ∧ s y = n

def start (x y n : Nat) : State :=
  Function.update (Function.update (fun _ => 0) x n) y 0

private def bodyPlus2 (x y : Nat) : Cmd :=
  .seq (.assign y (.add (.var y) (.const 2))) (.assign x (.sub (.var x) (.const 1)))

private def transferPlus2 (x y : Nat) : Cmd :=
  .while (loopGuard x) (bodyPlus2 x y)

private def spin : Cmd :=
  .while (.truth true) .skip

private def bodyReordered (c : Nat) : Cmd :=
  .seq (.assign c (.sub (.var c) (.const 1))) (.assign c (.add (.var c) (.const 1)))

theorem init_entails_inv (x y n : Nat) :
    (transferPre x y n).Entails (transferInv x y n) := by
  intro s h
  obtain ⟨hx, hy⟩ := h
  show s x + s y = n
  omega

#print axioms init_entails_inv

theorem body_preserves_inv (x y n : Nat) :
    Valid (fun s => transferInv x y n s ∧ (loopGuard x).eval s = true)
      (loopBody x y) (transferInv x y n) := by
  intro s s' hpre hstep
  obtain ⟨hinv, hguard⟩ := hpre
  have hstep' : BigStep
      (.seq (.assign y (.add (.var y) (.const 1)))
        (.assign x (.sub (.var x) (.const 1)))) s s' := hstep
  rw [BigStep.seq_iff] at hstep'
  obtain ⟨m, h1, h2⟩ := hstep'
  rw [BigStep.assign_iff] at h1 h2
  by_cases h : x = y
  · subst h
    have hinv' : s x + s x = n := hinv
    have e1 : m x = s x + 1 := by
      rw [h1, Function.update_self, AExp.eval_add, AExp.eval_var,
        AExp.eval_const]
    have e2 : s' x = m x - 1 := by
      rw [h2, Function.update_self, AExp.eval_sub, AExp.eval_var,
        AExp.eval_const]
    show s' x + s' x = n
    omega
  · have hguard' : (BExp.not (BExp.eq (.var x) (.const 0))).eval s = true :=
      hguard
    have hfalse : (BExp.eq (.var x) (.const 0)).eval s = false :=
      BExp.eval_not_eq_true.mp hguard'
    have hne0 : s x ≠ 0 := by
      intro heq
      have htrue : (BExp.eq (.var x) (.const 0)).eval s = true :=
        BExp.eval_eq_eq_true.mpr heq
      rw [hfalse] at htrue
      exact Bool.false_ne_true htrue
    have hinv' : s x + s y = n := hinv
    have emx : m x = s x := by
      rw [h1, Function.update_of_ne h]
    have emy : m y = s y + 1 := by
      rw [h1, Function.update_self, AExp.eval_add, AExp.eval_var,
        AExp.eval_const]
    have e2x : s' x = s x - 1 := by
      rw [h2, Function.update_self, AExp.eval_sub, AExp.eval_var,
        AExp.eval_const, emx]
    have hne' : y ≠ x := fun h' => h h'.symm
    have e2y : s' y = s y + 1 := by
      rw [h2, Function.update_of_ne hne', emy]
    show s' x + s' y = n
    omega

#print axioms body_preserves_inv

theorem exit_entails_post (x y n : Nat) :
    Assertion.Entails
      (fun s => transferInv x y n s ∧ (loopGuard x).eval s = false)
      (transferPost x y n) := by
  intro s h
  obtain ⟨hinv, hguard⟩ := h
  have hinv' : s x + s y = n := hinv
  have hguard' : (BExp.not (BExp.eq (.var x) (.const 0))).eval s = false :=
    hguard
  have heq0 : s x = 0 := by
    cases h' : (BExp.eq (.var x) (.const 0)).eval s with
    | true => exact BExp.eval_eq_eq_true.mp h'
    | false =>
        exfalso
        have htrue : (BExp.not (BExp.eq (.var x) (.const 0))).eval s = true :=
          BExp.eval_not_eq_true.mpr h'
        rw [hguard'] at htrue
        exact Bool.false_ne_true htrue
  have hpost : s x = 0 ∧ s y = n := ⟨heq0, by omega⟩
  exact hpost

#print axioms exit_entails_post

theorem body_decreases (x y : Nat) (hxy : x ≠ y) (k : Nat) :
    Valid (fun s => (loopGuard x).eval s = true ∧ transferVariant x s = k)
      (loopBody x y) (fun s => transferVariant x s < k) := by
  intro s s' hpre hstep
  obtain ⟨hguard, hvar⟩ := hpre
  have hvar' : s x = k := hvar
  have hguard' : (BExp.not (BExp.eq (.var x) (.const 0))).eval s = true :=
    hguard
  have hfalse : (BExp.eq (.var x) (.const 0)).eval s = false :=
    BExp.eval_not_eq_true.mp hguard'
  have hne0 : s x ≠ 0 := by
    intro heq
    have htrue : (BExp.eq (.var x) (.const 0)).eval s = true :=
      BExp.eval_eq_eq_true.mpr heq
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  have hstep' : BigStep
      (.seq (.assign y (.add (.var y) (.const 1)))
        (.assign x (.sub (.var x) (.const 1)))) s s' := hstep
  rw [BigStep.seq_iff] at hstep'
  obtain ⟨m, h1, h2⟩ := hstep'
  rw [BigStep.assign_iff] at h1 h2
  have emx : m x = s x := by
    rw [h1, Function.update_of_ne hxy]
  have e2x : s' x = s x - 1 := by
    rw [h2, Function.update_self, AExp.eval_sub, AExp.eval_var,
      AExp.eval_const, emx]
  show s' x < k
  omega

#print axioms body_decreases

theorem body_step (x y n : Nat) (hxy : x ≠ y) :
    ∀ s, transferInv x y n s → (loopGuard x).eval s = true →
      ∃ s', BigStep (loopBody x y) s s' ∧ transferInv x y n s' ∧
        transferVariant x s' < transferVariant x s := by
  intro s hinv hguard
  have hrun :=
    BigStep.seq (BigStep.assign s y (.add (.var y) (.const 1)))
      (BigStep.assign _ x (.sub (.var x) (.const 1)))
  refine ⟨_, hrun, ?_, ?_⟩
  · exact body_preserves_inv x y n ⟨hinv, hguard⟩ hrun
  · exact body_decreases x y hxy (s x) ⟨hguard, rfl⟩ hrun

#print axioms body_step

theorem transfer_valid (x y n : Nat) :
    Valid (transferPre x y n) (transfer x y) (transferPost x y n) := by
  have hloop : Valid (transferInv x y n) (transfer x y)
      (fun s => transferInv x y n s ∧ (loopGuard x).eval s = false) :=
    Valid.whileLoop (body_preserves_inv x y n)
  exact Valid.consequence (init_entails_inv x y n) hloop
    (exit_entails_post x y n)

#print axioms transfer_valid

theorem transfer_tvalid (x y n : Nat) (hxy : x ≠ y) :
    TValid (transferPre x y n) (transfer x y) (transferPost x y n) := by
  have hloop : TValid (transferInv x y n) (transfer x y)
      (fun s => transferInv x y n s ∧ (loopGuard x).eval s = false) :=
    TValid.whileVariant (invariant := transferInv x y n)
      (variant := transferVariant x) (body_step x y n hxy)
  exact TValid.consequence (init_entails_inv x y n) hloop
    (exit_entails_post x y n)

#print axioms transfer_tvalid

theorem start_pre (x y n : Nat) (hxy : x ≠ y) :
    transferPre x y n (start x y n) := by
  have hx : start x y n x = n := by
    show (Function.update (Function.update (fun _ => 0) x n) y 0) x = n
    rw [Function.update_of_ne hxy, Function.update_self]
  have hy : start x y n y = 0 := by
    show (Function.update (Function.update (fun _ => 0) x n) y 0) y = 0
    rw [Function.update_self]
  exact ⟨hx, hy⟩

#print axioms start_pre

theorem start_inv_guard :
    transferInv 0 1 3 (start 0 1 3) ∧ (loopGuard 0).eval (start 0 1 3) = true := by
  have h01 : (0 : Nat) ≠ 1 := by omega
  have hpre := start_pre 0 1 3 h01
  have hinv : transferInv 0 1 3 (start 0 1 3) :=
    init_entails_inv 0 1 3 hpre
  obtain ⟨hx, _hy⟩ := hpre
  have hguard : (loopGuard 0).eval (start 0 1 3) = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 3) with
    | true =>
        have heq0 : start 0 1 3 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  exact ⟨hinv, hguard⟩

#print axioms start_inv_guard

theorem run_n0 :
    ∃ s', BigStep (transfer 0 1) (start 0 1 0) s' ∧ s' 0 = 0 ∧ s' 1 = 0 := by
  have h01 : (0 : Nat) ≠ 1 := by omega
  have hpre := start_pre 0 1 0 h01
  obtain ⟨hx, hy⟩ := hpre
  have htrue : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 0) = true :=
    BExp.eval_eq_eq_true.mpr hx
  have hguard : (loopGuard 0).eval (start 0 1 0) = false := by
    cases h : (BExp.not (BExp.eq (.var 0) (.const 0))).eval (start 0 1 0) with
    | true =>
        exfalso
        have hfalse : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 0) = false :=
          BExp.eval_not_eq_true.mp h
        rw [htrue] at hfalse
        simp at hfalse
    | false => exact h
  have hrun : BigStep (transfer 0 1) (start 0 1 0) (start 0 1 0) :=
    BigStep.whileFalse hguard
  exact ⟨start 0 1 0, hrun, hx, hy⟩

#print axioms run_n0

theorem run_n3 :
    ∃ s', BigStep (transfer 0 1) (start 0 1 3) s' ∧ s' 0 = 0 ∧ s' 1 = 3 := by
  have h01 : (0 : Nat) ≠ 1 := by omega
  have h10 : (1 : Nat) ≠ 0 := by omega
  have hpre := start_pre 0 1 3 h01
  obtain ⟨hx0, hy0⟩ := hpre
  have g0 : (loopGuard 0).eval (start 0 1 3) = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 3) with
    | true =>
        have heq0 : start 0 1 3 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  have it1 : ∃ s1, BigStep (loopBody 0 1) (start 0 1 3) s1 ∧ s1 0 = 2 ∧
      s1 1 = 1 := by
    have hrun :=
      BigStep.seq (BigStep.assign (start 0 1 3) 1 (.add (.var 1) (.const 1)))
        (BigStep.assign _ 0 (.sub (.var 0) (.const 1)))
    refine ⟨_, hrun, ?_, ?_⟩
    · rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
          Function.update_of_ne h01]
      omega
    · rw [Function.update_of_ne h10, Function.update_self, AExp.eval_add,
          AExp.eval_var, AExp.eval_const]
      omega
  obtain ⟨s1, b0, hs10, hs11⟩ := it1
  have g1 : (loopGuard 0).eval s1 = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval s1 with
    | true =>
        have heq0 : s1 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  have it2 : ∃ s2, BigStep (loopBody 0 1) s1 s2 ∧ s2 0 = 1 ∧ s2 1 = 2 := by
    have hrun :=
      BigStep.seq (BigStep.assign s1 1 (.add (.var 1) (.const 1)))
        (BigStep.assign _ 0 (.sub (.var 0) (.const 1)))
    refine ⟨_, hrun, ?_, ?_⟩
    · rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
          Function.update_of_ne h01]
      omega
    · rw [Function.update_of_ne h10, Function.update_self, AExp.eval_add,
          AExp.eval_var, AExp.eval_const]
      omega
  obtain ⟨s2, b1, hs20, hs21⟩ := it2
  have g2 : (loopGuard 0).eval s2 = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval s2 with
    | true =>
        have heq0 : s2 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  have it3 : ∃ s3, BigStep (loopBody 0 1) s2 s3 ∧ s3 0 = 0 ∧ s3 1 = 3 := by
    have hrun :=
      BigStep.seq (BigStep.assign s2 1 (.add (.var 1) (.const 1)))
        (BigStep.assign _ 0 (.sub (.var 0) (.const 1)))
    refine ⟨_, hrun, ?_, ?_⟩
    · rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
          Function.update_of_ne h01]
      omega
    · rw [Function.update_of_ne h10, Function.update_self, AExp.eval_add,
          AExp.eval_var, AExp.eval_const]
      omega
  obtain ⟨s3, b2, hs30, hs31⟩ := it3
  have htrue : (BExp.eq (.var 0) (.const 0)).eval s3 = true :=
    BExp.eval_eq_eq_true.mpr hs30
  have g3 : (loopGuard 0).eval s3 = false := by
    cases h : (BExp.not (BExp.eq (.var 0) (.const 0))).eval s3 with
    | true =>
        exfalso
        have hfalse : (BExp.eq (.var 0) (.const 0)).eval s3 = false :=
          BExp.eval_not_eq_true.mp h
        rw [htrue] at hfalse
        simp at hfalse
    | false => exact h
  have r3 : BigStep (transfer 0 1) s3 s3 := BigStep.whileFalse g3
  have r2 : BigStep (transfer 0 1) s2 s3 := BigStep.whileTrue g2 b2 r3
  have r1 : BigStep (transfer 0 1) s1 s3 := BigStep.whileTrue g1 b1 r2
  have r0 : BigStep (transfer 0 1) (start 0 1 3) s3 :=
    BigStep.whileTrue g0 b0 r1
  exact ⟨s3, r0, hs30, hs31⟩

#print axioms run_n3

example : ∃ s', BigStep (transfer 0 1) (start 0 1 3) s' ∧ s' 0 = 0 ∧
    s' 1 = 3 := by
  have h01 : (0 : Nat) ≠ 1 := by omega
  obtain ⟨s', hrun, hpost⟩ := transfer_tvalid 0 1 3 h01 (start_pre 0 1 3 h01)
  exact ⟨s', hrun, hpost⟩

example (s' : State) (hrun : BigStep (transfer 0 1) (start 0 1 3) s') :
    s' 0 = 0 ∧ s' 1 = 3 := by
  have h01 : (0 : Nat) ≠ 1 := by omega
  exact transfer_valid 0 1 3 (start_pre 0 1 3 h01) hrun

theorem plus2_breaks_inv :
    ¬ Valid (fun s => transferInv 0 1 1 s ∧ (loopGuard 0).eval s = true)
      (bodyPlus2 0 1) (transferInv 0 1 1) := by
  intro hvalid
  have h01 : (0 : Nat) ≠ 1 := by omega
  have h10 : (1 : Nat) ≠ 0 := by omega
  have hpre := start_pre 0 1 1 h01
  have hinv : transferInv 0 1 1 (start 0 1 1) :=
    init_entails_inv 0 1 1 hpre
  obtain ⟨hx, hy⟩ := hpre
  have hguard : (loopGuard 0).eval (start 0 1 1) = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 1) with
    | true =>
        have heq0 : start 0 1 1 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  have hex : ∃ f, BigStep (bodyPlus2 0 1) (start 0 1 1) f ∧ f 0 = 0 ∧
      f 1 = 2 := by
    have hrun :=
      BigStep.seq
        (BigStep.assign (start 0 1 1) 1 (.add (.var 1) (.const 2)))
        (BigStep.assign _ 0 (.sub (.var 0) (.const 1)))
    refine ⟨_, hrun, ?_, ?_⟩
    · rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
          Function.update_of_ne h01]
      omega
    · rw [Function.update_of_ne h10, Function.update_self, AExp.eval_add,
          AExp.eval_var, AExp.eval_const]
      omega
  obtain ⟨f, hrun, hf0, hf1⟩ := hex
  have hconcl := hvalid ⟨hinv, hguard⟩ hrun
  have hconcl' : f 0 + f 1 = 1 := hconcl
  omega

#print axioms plus2_breaks_inv

theorem plus2_not_valid :
    ¬ Valid (transferPre 0 1 1) (transferPlus2 0 1) (transferPost 0 1 1) := by
  intro hvalid
  have h01 : (0 : Nat) ≠ 1 := by omega
  have h10 : (1 : Nat) ≠ 0 := by omega
  have hpre := start_pre 0 1 1 h01
  have hpre' := hpre
  obtain ⟨hx, hy⟩ := hpre'
  have hguard : (loopGuard 0).eval (start 0 1 1) = true := by
    cases h : (BExp.eq (.var 0) (.const 0)).eval (start 0 1 1) with
    | true =>
        have heq0 : start 0 1 1 0 = 0 := BExp.eval_eq_eq_true.mp h
        omega
    | false => exact BExp.eval_not_eq_true.mpr h
  have hex : ∃ f, BigStep (bodyPlus2 0 1) (start 0 1 1) f ∧ f 0 = 0 ∧
      f 1 = 2 := by
    have hrun :=
      BigStep.seq
        (BigStep.assign (start 0 1 1) 1 (.add (.var 1) (.const 2)))
        (BigStep.assign _ 0 (.sub (.var 0) (.const 1)))
    refine ⟨_, hrun, ?_, ?_⟩
    · rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
          Function.update_of_ne h01]
      omega
    · rw [Function.update_of_ne h10, Function.update_self, AExp.eval_add,
          AExp.eval_var, AExp.eval_const]
      omega
  obtain ⟨f, hb, hf0, hf1⟩ := hex
  have htrue : (BExp.eq (.var 0) (.const 0)).eval f = true :=
    BExp.eval_eq_eq_true.mpr hf0
  have hguard' : (loopGuard 0).eval f = false := by
    cases h : (BExp.not (BExp.eq (.var 0) (.const 0))).eval f with
    | true =>
        exfalso
        have hfalse : (BExp.eq (.var 0) (.const 0)).eval f = false :=
          BExp.eval_not_eq_true.mp h
        rw [htrue] at hfalse
        simp at hfalse
    | false => exact h
  have hrun : BigStep (transferPlus2 0 1) (start 0 1 1) f :=
    BigStep.whileTrue hguard hb (BigStep.whileFalse hguard')
  have hconcl := hvalid hpre hrun
  have hconcl' : f 0 = 0 ∧ f 1 = 1 := hconcl
  omega

#print axioms plus2_not_valid

theorem spin_valid (P Q : Assertion) :
    Valid P spin Q := by
  have hbody : Valid (fun s : State => True ∧ (BExp.truth true).eval s = true)
      .skip (fun _ => True) := by
    refine Valid.consequence ?_ (Valid.skip _) (Assertion.entails_refl _)
    intro s h
    exact h.1
  have hloop : Valid (fun _ : State => True) spin
      (fun s => True ∧ (BExp.truth true).eval s = false) :=
    Valid.whileLoop hbody
  refine Valid.consequence ?_ hloop ?_
  · intro s _
    exact True.intro
  · intro s h
    obtain ⟨_, hguard⟩ := h
    simp at hguard

#print axioms spin_valid

theorem spin_not_tvalid (x y n : Nat) (hxy : x ≠ y) (Q : Assertion) :
    ¬ TValid (transferPre x y n) spin Q := by
  intro htotal
  have hpre := start_pre x y n hxy
  obtain ⟨f, hrun, _hq⟩ := htotal hpre
  have hfalse := spin_valid (transferPre x y n) (fun _ => False) hpre hrun
  exact hfalse

#print axioms spin_not_tvalid

theorem alias_order_sensitive (c : Nat) (s : State) (h : s c = 0) :
    (∃ s₁, BigStep (loopBody c c) s s₁ ∧ s₁ c = 0) ∧
    (∃ s₂, BigStep (bodyReordered c) s s₂ ∧ s₂ c = 1) := by
  constructor
  · have hrun :=
      BigStep.seq (BigStep.assign s c (.add (.var c) (.const 1)))
        (BigStep.assign _ c (.sub (.var c) (.const 1)))
    refine ⟨_, hrun, ?_⟩
    rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
      Function.update_self, AExp.eval_add, AExp.eval_var, AExp.eval_const]
    omega
  · have hrun :=
      BigStep.seq (BigStep.assign s c (.sub (.var c) (.const 1)))
        (BigStep.assign _ c (.add (.var c) (.const 1)))
    refine ⟨_, hrun, ?_⟩
    rw [Function.update_self, AExp.eval_add, AExp.eval_var, AExp.eval_const,
      Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const]
    omega

#print axioms alias_order_sensitive

theorem alias_decrease_fails (c : Nat) :
    ¬ Valid (fun s => (loopGuard c).eval s = true ∧ transferVariant c s = 1)
      (loopBody c c) (fun s => transferVariant c s < 1) := by
  intro hvalid
  have hex : ∃ f, BigStep (loopBody c c) (Function.update (fun _ => 0) c 1) f ∧
      f c = 1 := by
    have hrun :=
      BigStep.seq
        (BigStep.assign (Function.update (fun _ => 0) c 1) c
          (.add (.var c) (.const 1)))
        (BigStep.assign _ c (.sub (.var c) (.const 1)))
    refine ⟨_, hrun, ?_⟩
    rw [Function.update_self, AExp.eval_sub, AExp.eval_var, AExp.eval_const,
      Function.update_self, AExp.eval_add, AExp.eval_var, AExp.eval_const,
      Function.update_self]
  obtain ⟨f, hrun, hf⟩ := hex
  have hpre : (loopGuard c).eval (Function.update (fun _ => 0) c 1) = true ∧
      transferVariant c (Function.update (fun _ => 0) c 1) = 1 := by
    constructor
    · cases h' : (BExp.eq (.var c) (.const 0)).eval
          (Function.update (fun _ => 0) c 1) with
      | true =>
          have heq0 : (Function.update (fun _ => 0) c 1) c = 0 :=
            BExp.eval_eq_eq_true.mp h'
          rw [Function.update_self] at heq0
          omega
      | false => exact BExp.eval_not_eq_true.mpr h'
    · show (Function.update (fun _ => 0) c 1) c = 1
      rw [Function.update_self]
  have hconcl := hvalid hpre hrun
  have hconcl' : f c < 1 := hconcl
  omega

#print axioms alias_decrease_fails

theorem alias_diverges (c : Nat) :
    Valid (fun s => s c = 1) (transfer c c) (fun _ => False) := by
  have hbody : Valid (fun s : State => s c = 1 ∧ (loopGuard c).eval s = true)
      (loopBody c c) (fun s => s c = 1) := by
    intro s s' hpre hstep
    obtain ⟨hinv, _hguard⟩ := hpre
    have hstep' : BigStep
        (.seq (.assign c (.add (.var c) (.const 1)))
          (.assign c (.sub (.var c) (.const 1)))) s s' := hstep
    rw [BigStep.seq_iff] at hstep'
    obtain ⟨m, h1, h2⟩ := hstep'
    rw [BigStep.assign_iff] at h1 h2
    have em : m c = s c + 1 := by
      rw [h1, Function.update_self, AExp.eval_add, AExp.eval_var,
        AExp.eval_const]
    have e2 : s' c = m c - 1 := by
      rw [h2, Function.update_self, AExp.eval_sub, AExp.eval_var,
        AExp.eval_const]
    show s' c = 1
    omega
  have hloop : Valid (fun s => s c = 1) (transfer c c)
      (fun s => s c = 1 ∧ (loopGuard c).eval s = false) :=
    Valid.whileLoop hbody
  refine Valid.consequence (Assertion.entails_refl _) hloop ?_
  intro s h
  obtain ⟨hinv, hguard⟩ := h
  have hguard' : (BExp.not (BExp.eq (.var c) (.const 0))).eval s = false :=
    hguard
  cases h' : (BExp.eq (.var c) (.const 0)).eval s with
  | true =>
      have heq0 : s c = 0 := BExp.eval_eq_eq_true.mp h'
      omega
  | false =>
      exfalso
      have htrue : (BExp.not (BExp.eq (.var c) (.const 0))).eval s = true :=
        BExp.eval_not_eq_true.mpr h'
      rw [hguard'] at htrue
      exact Bool.false_ne_true htrue

#print axioms alias_diverges

theorem alias_not_tvalid (c : Nat) (Q : Assertion) :
    ¬ TValid (fun s => s c = 1) (transfer c c) Q := by
  intro htotal
  have hw : (Function.update (fun _ => 0) c 1) c = 1 :=
    Function.update_self _ _ _
  obtain ⟨f, hrun, _hq⟩ := htotal hw
  have hfalse := alias_diverges c hw hrun
  exact hfalse

#print axioms alias_not_tvalid

example (c n : Nat) :
    Valid (transferPre c c n) (transfer c c) (transferPost c c n) :=
  transfer_valid c c n

end AtlasTeaching.IMPInvariants
