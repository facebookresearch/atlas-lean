/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.TuringMachines

namespace TuringMachine

variable {Q₁ Q₂ Γ : Type} [DecidableEq Q₁] [DecidableEq Q₂]

/--
Sequential composition of two Turing machines `M₁` and `M₂` sharing the same
tape alphabet `Γ`. The composite machine runs `M₁` first; whenever `M₁` would
halt (accept or reject) it transitions to `M₂.q₀` instead and continues with
`M₂`. The composite then accepts iff `M₂` accepts and rejects iff `M₂` rejects.
The state space `(Q₁ ⊕ Q₂) ⊕ Fin 2` keeps each machine's states in its own
copy and uses the final `Fin 2` for the new accept/reject states.
-/
noncomputable def TM.sequentialCompose
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) : TM ((Q₁ ⊕ Q₂) ⊕ Fin 2) Γ where
  blank := M₁.blank
  inputAlpha := M₁.inputAlpha
  blank_not_in_inputAlpha := M₁.blank_not_in_inputAlpha
  δ := fun q γ => match q with
    | .inl (.inl q₁) =>
      if q₁ = M₁.qAccept ∨ q₁ = M₁.qReject then
        (.inl (.inr M₂.q₀), γ, Direction.R)
      else
        let (q', b, d) := M₁.δ q₁ γ
        (.inl (.inl q'), b, d)
    | .inl (.inr q₂) =>
      if q₂ = M₂.qAccept then
        (.inr ⟨0, by omega⟩, γ, Direction.R)
      else if q₂ = M₂.qReject then
        (.inr ⟨1, by omega⟩, γ, Direction.R)
      else
        let (q', b, d) := M₂.δ q₂ γ
        (.inl (.inr q'), b, d)
    | .inr n => (.inr n, γ, Direction.R)
  q₀ := .inl (.inl M₁.q₀)
  qAccept := .inr ⟨0, by omega⟩
  qReject := .inr ⟨1, by omega⟩
  qReject_ne_qAccept := by simp

/--
Running a TM for `m + n` steps is the same as running it for `m` steps followed
by `n` steps. A basic additivity lemma for `TM.run`.
-/
theorem TM.run_add' {Q : Type} {Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c : Config Q Γ) (m n : ℕ) :
    M.run c (m + n) = M.run (M.run c m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    simp only [TM.run_succ, ih]

/--
Phase-1 simulation lemma: as long as `M₁` has not yet halted, running the
composite machine `sequentialCompose M₁ M₂` for `n` steps from a configuration
whose state lies in `inl ∘ inl` mirrors running `M₁` itself for `n` steps,
keeping the state, head position and tape in sync.
-/
theorem sequentialCompose_phase1_run
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (c : Config Q₁ Γ) (n : ℕ)
    (hNotHalt : ∀ k, k < n → ¬M₁.isHaltConfig (M₁.run c k)) :
    (TM.sequentialCompose M₁ M₂).run
      ⟨.inl (.inl c.state), c.headPos, c.tape⟩ n =
      ⟨.inl (.inl (M₁.run c n).state), (M₁.run c n).headPos, (M₁.run c n).tape⟩ := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    have hk : ∀ k, k < n → ¬M₁.isHaltConfig (M₁.run c k) :=
      fun k hk => hNotHalt k (Nat.lt_succ_of_lt hk)
    rw [TM.run, ih hk, TM.run]
    have hNotHaltN := hNotHalt n (Nat.lt_succ_of_le le_rfl)
    simp only [TM.step, TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig] at hNotHaltN ⊢
    push Not at hNotHaltN
    simp only [TM.sequentialCompose, hNotHaltN, or_self, ite_false, reduceCtorEq]

/--
Phase-2 simulation lemma: as long as `M₂` has not yet halted, running the
composite machine for `n` steps from a configuration whose state lies in
`inl ∘ inr` mirrors running `M₂` itself for `n` steps.
-/
theorem sequentialCompose_phase2_run
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (c : Config Q₂ Γ) (n : ℕ)
    (hNotHalt : ∀ k, k < n → ¬M₂.isHaltConfig (M₂.run c k)) :
    (TM.sequentialCompose M₁ M₂).run
      ⟨.inl (.inr c.state), c.headPos, c.tape⟩ n =
      ⟨.inl (.inr (M₂.run c n).state), (M₂.run c n).headPos, (M₂.run c n).tape⟩ := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    have hk : ∀ k, k < n → ¬M₂.isHaltConfig (M₂.run c k) :=
      fun k hk => hNotHalt k (Nat.lt_succ_of_lt hk)
    rw [TM.run, ih hk, TM.run]
    have hNotHaltN := hNotHalt n (Nat.lt_succ_of_le le_rfl)
    simp only [TM.step, TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig] at hNotHaltN ⊢
    push Not at hNotHaltN
    simp only [TM.sequentialCompose, hNotHaltN.1, hNotHaltN.2, ite_false, reduceCtorEq, false_or]

/--
The "handoff" step: when the composite machine is in a state corresponding to
either `M₁.qAccept` or `M₁.qReject`, one step transitions to `M₂.q₀` (without
modifying the tape), moving the head one cell to the right.
-/
theorem sequentialCompose_transition_step
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ)
    (q₁ : Q₁) (headPos : ℤ) (tape : Tape Γ)
    (hHalt : q₁ = M₁.qAccept ∨ q₁ = M₁.qReject) :
    (TM.sequentialCompose M₁ M₂).step
      ⟨.inl (.inl q₁), headPos, tape⟩ =
      ⟨.inl (.inr M₂.q₀), headPos + 1, tape⟩ := by
  simp only [TM.step, TM.sequentialCompose]
  simp [hHalt]

/--
The starting configuration of `M₂` in the composite execution: take the
configuration `M₁` reaches after `n₁` steps on input `w`, move the head one cell
right, and set the state to `M₂.q₀`.
-/
noncomputable def phase2InitConfig
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (w : List Γ) (n₁ : ℕ) : Config Q₂ Γ :=
  let c₁ := M₁.runOnInput w n₁
  ⟨M₂.q₀, c₁.headPos + 1, c₁.tape⟩

/--
Specialisation of `sequentialCompose_phase1_run` starting from the composite
machine's initial configuration on input `w`: provided `M₁` does not halt in
fewer than `n₁` steps, after `n₁` steps the composite tracks `M₁.runOnInput w n₁`.
-/
theorem sequentialCompose_phase1_from_init
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (w : List Γ) (n₁ : ℕ)
    (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k)) :
    let M₃ := TM.sequentialCompose M₁ M₂
    M₃.run (M₃.initConfig w) n₁ =
      ⟨.inl (.inl (M₁.runOnInput w n₁).state),
       (M₁.runOnInput w n₁).headPos,
       (M₁.runOnInput w n₁).tape⟩ := by
  show (TM.sequentialCompose M₁ M₂).run
    ⟨.inl (.inl M₁.q₀), 0, (M₁.initConfig w).tape⟩ n₁ = _
  conv_lhs =>
    rw [show (⟨Sum.inl (Sum.inl M₁.q₀), (0 : ℤ), (M₁.initConfig w).tape⟩ :
      Config ((Q₁ ⊕ Q₂) ⊕ Fin 2) Γ) =
      ⟨.inl (.inl (M₁.initConfig w).state), (M₁.initConfig w).headPos,
       (M₁.initConfig w).tape⟩ from by simp [TM.initConfig]]
  exact sequentialCompose_phase1_run M₁ M₂ (M₁.initConfig w) n₁ hNotHalt₁

/--
Acceptance of the sequential composition: if `M₁` halts after exactly `n₁`
steps on `w`, and `M₂` started in `phase2InitConfig M₁ M₂ w n₁` halts in the
accept state after exactly `n₂` steps, then `sequentialCompose M₁ M₂` accepts
`w` (in `n₁ + 1 + n₂ + 1` steps).
-/
theorem sequentialCompose_accepts_of_phases
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (w : List Γ)
    (n₁ : ℕ) (hHalt₁ : M₁.isHaltConfig (M₁.runOnInput w n₁))
    (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k))
    (n₂ : ℕ)
    (hAccept₂ : M₂.isAcceptConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) n₂))
    (hNotHalt₂ : ∀ k, k < n₂ → ¬M₂.isHaltConfig (M₂.run
      (phase2InitConfig M₁ M₂ w n₁) k)) :
    (TM.sequentialCompose M₁ M₂).accepts w := by
  let M₃ := TM.sequentialCompose M₁ M₂
  let c₂ := phase2InitConfig M₁ M₂ w n₁
  refine ⟨n₁ + 1 + n₂ + 1, ?_⟩
  have h1 := sequentialCompose_phase1_from_init M₁ M₂ w n₁ hNotHalt₁
  have h2 : M₃.run (M₃.initConfig w) (n₁ + 1) =
      ⟨.inl (.inr M₂.q₀), (M₁.runOnInput w n₁).headPos + 1,
       (M₁.runOnInput w n₁).tape⟩ := by
    rw [TM.run_succ, h1]
    exact sequentialCompose_transition_step M₁ M₂ _ _ _
      (by rcases hHalt₁ with h | h <;> [left; right] <;> exact h)
  have h3 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂) =
      ⟨.inl (.inr (M₂.run c₂ n₂).state),
       (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_add', h2]
    exact sequentialCompose_phase2_run M₁ M₂ c₂ n₂ hNotHalt₂
  have hAcc_state : (M₂.run c₂ n₂).state = M₂.qAccept := hAccept₂
  have h4 : M₃.step ⟨.inl (.inr (M₂.run c₂ n₂).state),
       (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ =
      ⟨.inr ⟨0, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
       (M₂.run c₂ n₂).tape⟩ := by
    simp only [hAcc_state]
    show (TM.sequentialCompose M₁ M₂).step
      ⟨.inl (.inr M₂.qAccept), (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ = _
    simp only [TM.step, TM.sequentialCompose]
    simp
  have h5 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂ + 1) =
      ⟨.inr ⟨0, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
       (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_succ, h3, h4]
  show M₃.isAcceptConfig (M₃.runOnInput w (n₁ + 1 + n₂ + 1))
  show (M₃.runOnInput w (n₁ + 1 + n₂ + 1)).state = M₃.qAccept
  simp only [TM.runOnInput, h5]
  rfl

/--
Rejection of the sequential composition: if `M₁` halts after `n₁` steps on `w`
and `M₂` started in `phase2InitConfig M₁ M₂ w n₁` halts in the reject state
after `n₂` steps, then `sequentialCompose M₁ M₂` rejects `w`.
-/
theorem sequentialCompose_rejects_of_phases
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ) (w : List Γ)
    (n₁ : ℕ) (hHalt₁ : M₁.isHaltConfig (M₁.runOnInput w n₁))
    (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k))
    (n₂ : ℕ)
    (hReject₂ : M₂.isRejectConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) n₂))
    (hNotHalt₂ : ∀ k, k < n₂ → ¬M₂.isHaltConfig (M₂.run
      (phase2InitConfig M₁ M₂ w n₁) k)) :
    (TM.sequentialCompose M₁ M₂).rejects w := by
  let M₃ := TM.sequentialCompose M₁ M₂
  let c₂ := phase2InitConfig M₁ M₂ w n₁
  refine ⟨n₁ + 1 + n₂ + 1, ?_⟩
  have h1 := sequentialCompose_phase1_from_init M₁ M₂ w n₁ hNotHalt₁
  have h2 : M₃.run (M₃.initConfig w) (n₁ + 1) =
      ⟨.inl (.inr M₂.q₀), (M₁.runOnInput w n₁).headPos + 1,
       (M₁.runOnInput w n₁).tape⟩ := by
    rw [TM.run_succ, h1]
    exact sequentialCompose_transition_step M₁ M₂ _ _ _
      (by rcases hHalt₁ with h | h <;> [left; right] <;> exact h)
  have h3 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂) =
      ⟨.inl (.inr (M₂.run c₂ n₂).state),
       (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_add', h2]
    exact sequentialCompose_phase2_run M₁ M₂ c₂ n₂ hNotHalt₂
  have hRej_state : (M₂.run c₂ n₂).state = M₂.qReject := hReject₂
  have h4 : M₃.step ⟨.inl (.inr (M₂.run c₂ n₂).state),
       (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ =
      ⟨.inr ⟨1, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
       (M₂.run c₂ n₂).tape⟩ := by
    simp only [hRej_state]
    show (TM.sequentialCompose M₁ M₂).step
      ⟨.inl (.inr M₂.qReject), (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ = _
    simp only [TM.step, TM.sequentialCompose]
    simp [M₂.qReject_ne_qAccept]
  have h5 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂ + 1) =
      ⟨.inr ⟨1, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
       (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_succ, h3, h4]
  show M₃.isRejectConfig (M₃.runOnInput w (n₁ + 1 + n₂ + 1))
  show (M₃.runOnInput w (n₁ + 1 + n₂ + 1)).state = M₃.qReject
  simp only [TM.runOnInput, h5]
  rfl

end TuringMachine
