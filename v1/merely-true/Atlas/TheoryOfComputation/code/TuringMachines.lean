/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.RelClasses
namespace TuringMachine

/-- The two possible directions in which a Turing machine head can move on each
step: `L` for left, `R` for right. -/
inductive Direction where
  | L : Direction
  | R : Direction
  deriving DecidableEq, Repr, Inhabited

open Direction

/-- A Turing machine, formalizing Sipser's 7-tuple `(Q, Σ, Γ, δ, q₀, q_acc, q_rej)`:
* `Q` is the set of states,
* `Γ` is the tape alphabet containing a distinguished `blank` symbol,
* `inputAlpha ⊆ Γ` is the input alphabet (excluding `blank`),
* `δ : Q × Γ → Q × Γ × {L, R}` is the transition function,
* `q₀`, `qAccept`, `qReject` are the start, accept and reject states (with
  `qReject ≠ qAccept`). -/
structure TM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

/-- A (two-way infinite) Turing-machine tape: a function from cell index `ℤ` to
tape-alphabet symbols. -/
abbrev Tape (Γ : Type) := ℤ → Γ

/-- A configuration of a Turing machine: current `state`, head position `headPos`
on the tape, and the full tape contents `tape`. -/
structure Config (Q : Type) (Γ : Type) where
  state : Q
  headPos : ℤ
  tape : Tape Γ

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- One computation step of `M`: if the current state is `qAccept` or `qReject`
the configuration is fixed; otherwise apply `δ` to write a new symbol, move the
head left or right, and update the state. -/
def TM.step (M : TM Q Γ) (c : Config Q Γ) : Config Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let (q', b, d) := M.δ c.state (c.tape c.headPos)
    { state := q'
      headPos := match d with
        | Direction.L => c.headPos - 1
        | Direction.R => c.headPos + 1
      tape := Function.update c.tape c.headPos b }

/-- The initial configuration of `M` on input `w`: state `q₀`, head at position
`0`, and the tape containing `w` at positions `0, …, |w|-1` with blanks elsewhere. -/
def TM.initConfig (M : TM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- Iterate `M.step` starting from configuration `c` for `n` steps. -/
def TM.run (M : TM Q Γ) (c : Config Q Γ) : ℕ → Config Q Γ
  | 0 => c
  | n + 1 => M.step (M.run c n)

/-- The configuration of `M` after running `n` steps on input `w`, starting
from `M.initConfig w`. -/
def TM.runOnInput (M : TM Q Γ) (w : List Γ) (n : ℕ) : Config Q Γ :=
  M.run (M.initConfig w) n

/-- A configuration is "accepting" if its state equals `M.qAccept`. -/
def TM.isAcceptConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration is "rejecting" if its state equals `M.qReject`. -/
def TM.isRejectConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- A configuration is "halting" if it is either accepting or rejecting. -/
def TM.isHaltConfig (M : TM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- `M` accepts the input `w` if at some step `n` the computation enters
`qAccept`. -/
def TM.accepts (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isAcceptConfig (M.runOnInput w n)

/-- `M` rejects the input `w` (by halting) if at some step `n` the computation
enters `qReject`. -/
def TM.rejects (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isRejectConfig (M.runOnInput w n)

/-- `M` halts on input `w` if it reaches a halting (accept or reject)
configuration after some number of steps. -/
def TM.halts (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isHaltConfig (M.runOnInput w n)

/-- The language `L(M)` recognized by `M`: the set of inputs `w` that `M`
accepts. -/
def TM.language (M : TM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- `c₁` yields `c₂` in one step: `c₁` is not a halting configuration and
`M.step c₁ = c₂`. -/
def TM.yields (M : TM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ¬M.isHaltConfig c₁ ∧ M.step c₁ = c₂

/-- The reflexive-transitive closure of one-step yielding: `c₁` reaches `c₂`
after some finite number of computation steps. -/
def TM.yieldsMulti (M : TM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ∃ n : ℕ, M.run c₁ n = c₂

/-- `M` has an accepting computation history on `w`: at some step `n` the
configuration is in `qAccept`. (Same as `M.accepts w`.) -/
def TM.hasAcceptingHistory (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, M.isAcceptConfig (M.runOnInput w n)

/-- `M` is a decider: it halts on every input (never loops forever). -/
def TM.isDecider (M : TM Q Γ) : Prop :=
  ∀ w : List Γ, M.halts w

/-- A language `A` is Turing-recognizable if there is some Turing machine `M`
with `L(M) = A`. -/
def IsTuringRecognizable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ), M.language = A

/-- A language `A` is Turing-decidable if some TM decider `M` (a TM that halts
on every input) satisfies `L(M) = A`. -/
def IsTuringDecidable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ), M.isDecider ∧ M.language = A

/-- `M` decides `A` if `M` is a decider and `L(M) = A`. -/
def TM.decides (M : TM Q Γ) (A : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = A

/-- Stepping an accepting configuration leaves it unchanged. -/
theorem TM.step_of_accept (M : TM Q Γ) (c : Config Q Γ)
    (h : M.isAcceptConfig c) : M.step c = c := by
  simp only [TM.step, TM.isAcceptConfig] at *
  simp [h]

/-- Stepping a rejecting configuration leaves it unchanged. -/
theorem TM.step_of_reject (M : TM Q Γ) (c : Config Q Γ)
    (h : M.isRejectConfig c) : M.step c = c := by
  simp only [TM.step, TM.isRejectConfig] at *
  simp [h]

/-- Halting configurations (accept or reject) are fixed points of `M.step`. -/
theorem TM.step_of_halt (M : TM Q Γ) (c : Config Q Γ)
    (h : M.isHaltConfig c) : M.step c = c := by
  rcases h with h | h
  · exact M.step_of_accept c h
  · exact M.step_of_reject c h

/-- Acceptance is stable under further steps: once accepted, always accepted. -/
theorem TM.accepts_stable (M : TM Q Γ) (c : Config Q Γ) (n : ℕ)
    (h : M.isAcceptConfig c) : M.isAcceptConfig (M.run c n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [TM.run]
    rw [M.step_of_accept _ ih]
    exact ih

/-- Running a TM from any halting configuration for any number of steps leaves
the configuration unchanged. -/
theorem TM.run_of_isHaltConfig (M : TM Q Γ) (c : Config Q Γ) (n : ℕ)
    (h : M.isHaltConfig c) : M.run c n = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.run]
    rw [ih]
    exact M.step_of_halt c h

/-- Running for `0` steps returns the same configuration. -/
@[simp]
theorem TM.run_zero (M : TM Q Γ) (c : Config Q Γ) : M.run c 0 = c := rfl

/-- Unfolding lemma: running for `n + 1` steps equals one `step` after running
for `n` steps. -/
@[simp]
theorem TM.run_succ (M : TM Q Γ) (c : Config Q Γ) (n : ℕ) :
    M.run c (n + 1) = M.step (M.run c n) := rfl

/-- A Linearly Bounded Automaton (LBA): a 1-tape Turing machine whose head can
never move off the input portion of the tape. Formally, on every input `w` and
every step `n`, the head position lies in `[0, max 1 |w|)`. -/
structure LBA (Q : Type) (Γ : Type) [DecidableEq Q] where
  toTM : TM Q Γ
  head_bounded : ∀ (w : List Γ) (n : ℕ),
    let c := toTM.runOnInput w n
    0 ≤ c.headPos ∧ c.headPos < ↑(max 1 w.length)

/-- An LBA `B` accepts `w` iff its underlying TM accepts `w`. -/
def LBA.accepts (B : LBA Q Γ) (w : List Γ) : Prop :=
  B.toTM.accepts w

/-- The language recognized by an LBA, inherited from its underlying TM. -/
def LBA.language (B : LBA Q Γ) : Set (List Γ) :=
  B.toTM.language

/-- An LBA is a decider iff its underlying TM halts on every input. -/
def LBA.isDecider (B : LBA Q Γ) : Prop :=
  B.toTM.isDecider

/-- A Turing enumerator: a deterministic TM together with a "printing"
predicate `prints` specifying which strings have been output by step `n`
(viewing each `Config` as the state of the enumerator after some number of
steps). The enumerated language is the union of these print sets. -/
structure TuringEnumerator (Q : Type) (Γ : Type) [DecidableEq Q] where
  toTM : TM Q Γ
  prints : Config Q Γ → Set (List Γ)

/-- The initial configuration of an enumerator: start state, head at `0`, and
an all-blank tape. -/
def TuringEnumerator.initConfig (E : TuringEnumerator Q Γ) : Config Q Γ where
  state := E.toTM.q₀
  headPos := 0
  tape := fun _ => E.toTM.blank

/-- The configuration of the enumerator after `n` steps. -/
def TuringEnumerator.run (E : TuringEnumerator Q Γ) (n : ℕ) : Config Q Γ :=
  E.toTM.run E.initConfig n

/-- The language `L(E)` enumerated by `E`: all strings `w` that appear in the
print set of some run-step configuration. -/
def TuringEnumerator.language (E : TuringEnumerator Q Γ) : Set (List Γ) :=
  {w | ∃ n : ℕ, w ∈ E.prints (E.run n)}

/-- A language `A` is Turing-enumerable if there is a Turing enumerator `E`
with `L(E) = A`. -/
def IsTuringEnumerable (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (E : TuringEnumerator Q Γ), E.language = A

/-- An auxiliary "counting" TM with state set `ℕ`: it starts in state `2`, never
halts (it never reaches the accept state `0` or reject state `1`), and on each
step increments its state by `1`. Used as the driver for enumerators built from
recognizers. -/
noncomputable def countingTM (blank : Γ) (inputAlpha : Set Γ) (h : blank ∉ inputAlpha) :
    TM ℕ Γ where
  blank := blank
  inputAlpha := inputAlpha
  blank_not_in_inputAlpha := h
  δ := fun q γ => (q + 1, γ, Direction.R)
  q₀ := 2
  qAccept := 0
  qReject := 1
  qReject_ne_qAccept := by omega

/-- One step of `countingTM` from a non-halting state (state `≥ 2`) increments
the state by `1`. -/
lemma countingTM_step_state {Γ : Type} (blank : Γ) (inputAlpha : Set Γ) (h : blank ∉ inputAlpha)
    (c : Config ℕ Γ) (hc : c.state ≥ 2) :
    ((countingTM blank inputAlpha h).step c).state = c.state + 1 := by
  simp only [TM.step, countingTM]
  have h1 : ¬(c.state = 0 ∨ c.state = 1) := by omega
  simp [h1]

/-- Running `countingTM` for `n` steps starting from state `2` reaches state
`2 + n`; in particular, the step count can be read off from the state. -/
lemma countingTM_run_state {Γ : Type} (blank : Γ) (inputAlpha : Set Γ) (h : blank ∉ inputAlpha)
    (c : Config ℕ Γ) (hc : c.state = 2) (n : ℕ) :
    ((countingTM blank inputAlpha h).run c n).state = 2 + n := by
  induction n with
  | zero => simp [TM.run, hc]
  | succ n ih =>
    simp only [TM.run]
    rw [countingTM_step_state]
    · omega
    · omega

/-- Forward direction of the equivalence "T-recognizable ↔ T-enumerable":
every Turing-recognizable language is Turing-enumerable. The proof simulates
the recognizer `M` step-by-step on every input `w`, printing `w` exactly when
`M` accepts `w` within the current step budget. -/
theorem isTuringEnumerable_of_isTuringRecognizable {Γ : Type} {A : Set (List Γ)}
    (h : IsTuringRecognizable A) : IsTuringEnumerable A := by
  obtain ⟨Q_M, hDecEq, M, hLang⟩ := h
  letI : DecidableEq Q_M := hDecEq
  let cTM := countingTM M.blank M.inputAlpha M.blank_not_in_inputAlpha
  let E : TuringEnumerator ℕ Γ := {
    toTM := cTM
    prints := fun c => {w | M.isAcceptConfig (M.runOnInput w (c.state - 2))}
  }
  refine ⟨ℕ, inferInstance, E, ?_⟩
  subst hLang
  ext w
  simp only [TuringEnumerator.language, Set.mem_setOf_eq, TM.language, TM.accepts]
  constructor
  · rintro ⟨n, hw⟩
    have hstate : (E.run n).state = 2 + n := by
      simp only [TuringEnumerator.run, E, cTM]
      apply countingTM_run_state
      simp [TuringEnumerator.initConfig, countingTM]
    change M.isAcceptConfig (M.runOnInput w ((E.run n).state - 2)) at hw
    rw [hstate] at hw
    simp only [Nat.add_sub_cancel_left] at hw
    exact ⟨n, hw⟩
  · rintro ⟨n, hw⟩
    refine ⟨n, ?_⟩
    change M.isAcceptConfig (M.runOnInput w ((E.run n).state - 2))
    have hstate : (E.run n).state = 2 + n := by
      simp only [TuringEnumerator.run, E, cTM]
      apply countingTM_run_state
      simp [TuringEnumerator.initConfig, countingTM]
    rw [hstate]
    simp only [Nat.add_sub_cancel_left]
    exact hw



/-- `M` halts on `w` within the time bound `t`: there is some step count
`n ≤ t` at which `M` is already in a halting configuration. -/
def TM.haltsWithin (M : TM Q Γ) (w : List Γ) (t : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ t ∧ M.isHaltConfig (M.runOnInput w n)

/-- `M` decides `A` in time `f`: `M` decides `A`, and on every input `w` of
length `n` it halts within `f n` steps. -/
def TM.decidesInTime (M : TM Q Γ) (A : Set (List Γ)) (f : ℕ → ℕ) : Prop :=
  M.decides A ∧ ∀ w : List Γ, M.haltsWithin w (f w.length)

/-- `A` is decidable in (big-O) time `f`: some TM `M` decides `A` within
`c · f n` steps on inputs of length `n`, for some positive constant `c`. -/
def IsDecidableInTime (A : Set (List Γ)) (f : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : TM Q Γ) (c : ℕ),
    0 < c ∧ M.decidesInTime A (fun n => c * f n)

/-- A working tape alphabet for the language `{a^k b^k}` decider: input symbols
`a` and `b`, plus a marker `cross` (used to cross off symbols during scanning)
and a `blank`. -/
inductive ABSymbol where
  | a : ABSymbol
  | b : ABSymbol
  | cross : ABSymbol
  | blank : ABSymbol
  deriving DecidableEq, Repr, Inhabited

open ABSymbol in
/-- The classic non-regular language `A = {a^k b^k | k ≥ 0}` over the alphabet
`{a, b}`. -/
def lang_akbk : Set (List ABSymbol) :=
  {w | ∃ k : ℕ, w = List.replicate k ABSymbol.a ++ List.replicate k ABSymbol.b}

/-- The time-bound function `n · (⌊log₂ n⌋ + 1)`, used as an upper estimate for
`O(n log n)` running times. -/
def nlogn (n : ℕ) : ℕ := n * (Nat.log 2 n + 1)


end TuringMachine
