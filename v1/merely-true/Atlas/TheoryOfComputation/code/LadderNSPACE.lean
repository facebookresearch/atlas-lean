/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.SpaceComplexity

open Computability TuringMachine SpaceComplexity

namespace SpaceComplexity

/-- Tape alphabet used by the linear-space NTM deciding `LADDER_DFA`.
It consists of the input symbols of the DFA (`ofAlpha`), a `separator` used to encode the
pair `⟨u, v⟩`, and a `blank` symbol. -/
inductive LadderTapeSymbol (α : Type) : Type
  | ofAlpha : α → LadderTapeSymbol α
  | separator : LadderTapeSymbol α
  | blank : LadderTapeSymbol α
  deriving DecidableEq

/-- The default tape symbol is `blank`. -/
instance {α : Type} : Inhabited (LadderTapeSymbol α) := ⟨LadderTapeSymbol.blank⟩

/-- Encoding of a pair of strings `(u, v)` on the tape as `u ++ [separator] ++ v`,
where each symbol of `u` and `v` is lifted via `ofAlpha`. -/
def encodePair {α : Type} (u v : List α) : List (LadderTapeSymbol α) :=
  u.map LadderTapeSymbol.ofAlpha ++ [LadderTapeSymbol.separator] ++
  v.map LadderTapeSymbol.ofAlpha

/-- The on-tape language version of `LADDER_DFA`: tape words `w` that encode some pair `(u, v)`
of strings such that there is a ladder `y₁, …, y_k ∈ L(B)` of common-length strings (consecutive
ones differing in a single symbol) with `y₁ = u` and `y_k = v`. -/
def LADDER_DFA_Lang {α : Type} {σ : Type} [Fintype σ] [Fintype α]
    (B : DFA α σ) : Set (List (LadderTapeSymbol α)) :=
  {w | ∃ (u v : List α), w = encodePair u v ∧ LADDER_DFA B u v}

/-- The phases of the linear-space NTM that decides `LADDER_DFA`.
- `readInput`: reading and buffering the input pair `⟨u, v⟩` from the tape.
- `searchFwd`: nondeterministically guessing the next rung of the ladder.
- `searchBack`: moving the head back to the working area between rungs.
- `accepted` / `rejected`: terminal states. -/
inductive LadderPhase
  | readInput | searchFwd | searchBack | accepted | rejected
  deriving DecidableEq, Fintype

/-- Internal control state of the `LADDER_DFA` NTM.
- `phase` is the current phase.
- `buf` is the buffered tape input being parsed in `readInput`.
- `y` is the current rung of the ladder (a string in `L(B)` of the common length).
- `v` is the target endpoint of the ladder.
- `counter` bounds the number of remaining rungs to try (so the machine halts).

Note: the components `buf`, `y`, `v` are stored inside the state for convenience but represent
information that fits in `O(n)` tape cells in the simulating linear-space NTM. -/
structure LadderState (α : Type) where
  phase : LadderPhase
  buf : List (LadderTapeSymbol α)
  y : List α
  v : List α
  counter : ℕ
  deriving DecidableEq

/-- Transition relation of the linear-space NTM deciding `LADDER_DFA`.
At the end of `readInput` it parses the buffer into a pair `(u, v)` of equal-length strings with
`u ∈ L(B)`, and either accepts immediately (if `u = v`) or enters `searchFwd` with `y := u` and
`counter := |α|^|u|` (the maximum possible number of rungs without repetition).
In `searchFwd` it nondeterministically guesses a position `i` and symbol `a`, sets
`y[i] := a`, checks that the new rung is in `L(B)`, and either accepts (if it equals `v`) or
continues. `searchBack` simply moves the head left between rungs. -/
noncomputable def ladderNTMδ {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) (q : LadderState α) (sym : LadderTapeSymbol α) :
    Set (LadderState α × LadderTapeSymbol α × Direction) := by
  classical
  exact match q.phase with
  | .readInput =>
      match sym with
      | .blank =>


        if h : ∃ (u v : List α), q.buf = encodePair u v ∧
            u.length = v.length ∧ u ∈ B.accepts then
          let u := h.choose
          let v := h.choose_spec.choose
          if u = v then

            {(⟨.accepted, [], [], [], 0⟩, sym, Direction.R)}
          else if u ∈ B.accepts then

            {(⟨.searchFwd, [], u, v, (Fintype.card α) ^ u.length⟩, sym, Direction.R)}
          else
            {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
        else
          {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      | other => {(⟨.readInput, q.buf ++ [other], [], [], 0⟩, sym, Direction.R)}
  | .searchFwd =>


      if q.counter = 0 then

        {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      else if h_len : q.y.length = 0 then

        {(⟨.rejected, [], [], [], 0⟩, sym, Direction.R)}
      else

        (Set.univ : Set (Fin q.y.length × α)).image fun ⟨i, a⟩ =>
          let new_y := q.y.set i.val a
          if ¬(new_y ∈ B.accepts) then
            (⟨.rejected, [], [], [], 0⟩, sym, Direction.R)
          else if new_y = q.v then
            (⟨.accepted, [], [], [], 0⟩, sym, Direction.R)
          else
            (⟨.searchBack, [], new_y, q.v, q.counter - 1⟩, sym, Direction.R)
  | .searchBack =>

      {(⟨.searchFwd, [], q.y, q.v, q.counter⟩, sym, Direction.L)}
  | .accepted => ∅
  | .rejected => ∅

/-- The linear-space NTM deciding `LADDER_DFA` for the DFA `B`. The state space is
`LadderState α`, the tape alphabet is `LadderTapeSymbol α`, and the transition relation is
`ladderNTMδ B`. The input alphabet consists of the lifted DFA symbols and the separator. -/
noncomputable def ladderNTM {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) :
    NTM (LadderState α) (LadderTapeSymbol α) where
  blank := .blank
  inputAlpha := Set.range LadderTapeSymbol.ofAlpha ∪ {LadderTapeSymbol.separator}
  blank_not_in_inputAlpha := by
    intro hmem
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨a, h⟩ | h <;> cases h
  δ := ladderNTMδ B
  q₀ := ⟨.readInput, [], [], [], 0⟩
  qAccept := ⟨.accepted, [], [], [], 0⟩
  qReject := ⟨.rejected, [], [], [], 0⟩
  qReject_ne_qAccept := by simp [LadderState.mk.injEq]







/-- A uniform encoding scheme for triples `⟨B, u, v⟩` over a single fixed tape alphabet `Γ`,
suitable for stating `LADDER_DFA` as a single language. It packages:
- a tape alphabet `Γ`;
- an encoding function `encode` for any DFA `B` and strings `u, v`;
- a decidable validity predicate `isValidEncoding` characterising the image of `encode`;
- and a lower bound `|u| + |v| ≤ |encode B u v|` ensuring that the encoded input is at least
  as long as the data it represents (so a linear-space bound on the encoding translates back
  to a linear bound on the underlying strings). -/
structure DFAEncoding where
  Γ : Type
  encode : {α : Type} → {σ : Type} → [Fintype α] → [Fintype σ] →
    (B : DFA α σ) → (u v : List α) → List Γ
  isValidEncoding : List Γ → Prop
  isValidEncoding_iff : ∀ w : List Γ, isValidEncoding w ↔
    ∃ (α : Type) (σ : Type) (_ : Fintype α) (_ : Fintype σ),
      ∃ (B : DFA α σ) (u v : List α), w = encode B u v
  encode_length_lower_bound : {α : Type} → {σ : Type} → [Fintype α] → [Fintype σ] →
    (B : DFA α σ) → (u v : List α) →
    u.length + v.length ≤ (encode B u v).length

/-- The uniform formulation `LADDER_DFA = {⟨B, u, v⟩ | B is a DFA and there is a ladder in
`L(B)` from `u` to `v`}` over a fixed tape alphabet, using a `DFAEncoding`. -/
def LADDER_DFA_Uniform (enc : DFAEncoding) : Set (List enc.Γ) :=
  {w | ∃ (α : Type) (σ : Type) (_ : Fintype α) (_ : DecidableEq α)
         (_ : Fintype σ) (_ : DecidableEq σ)
         (B : DFA α σ) (u v : List α),
       w = enc.encode B u v ∧ LADDER_DFA B u v}



end SpaceComplexity
