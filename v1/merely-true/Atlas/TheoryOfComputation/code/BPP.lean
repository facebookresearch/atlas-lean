/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.Complexity
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

namespace TuringMachine

open TuringMachine

/-- A Probabilistic Turing Machine (PTM): a deterministic 1-tape TM augmented with
two transition functions `δ₀` and `δ₁`. At each step the machine flips a fair coin
and uses `δ₀` on outcome `0` and `δ₁` on outcome `1`. -/
structure PTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ₀ : Q → Γ → Q × Γ × Direction
  δ₁ : Q → Γ → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- Advance the PTM `M` by one step from configuration `c` using the given coin
flip: chooses `δ₁` when `coin = true` and `δ₀` otherwise. Halting configurations
(accept/reject) are fixed points. -/
def PTM.stepWithCoin (M : PTM Q Γ) (c : Config Q Γ) (coin : Bool) : Config Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let (q', b, d) := if coin then M.δ₁ c.state (c.tape c.headPos)
                              else M.δ₀ c.state (c.tape c.headPos)
    let newHeadPos := match d with
      | Direction.L => c.headPos - 1
      | Direction.R => c.headPos + 1
    ⟨q', newHeadPos, Function.update c.tape c.headPos b⟩

/-- The starting configuration of `M` on input `w`: the head is at position `0`,
the state is `q₀`, and the tape holds the symbols of `w` with blanks elsewhere. -/
def PTM.initConfig (M : PTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- Run the PTM `M` on input `w` for `n` steps, consuming the sequence `coins`
of `n` coin flips and returning the resulting configuration. -/
def PTM.runWithCoins (M : PTM Q Γ) (w : List Γ) : (n : ℕ) → (Fin n → Bool) → Config Q Γ
  | 0, _ => M.initConfig w
  | n + 1, coins =>
    let prevCoins : Fin n → Bool := fun i => coins i.castSucc
    let prevConfig := M.runWithCoins w n prevCoins
    M.stepWithCoin prevConfig (coins ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- A configuration `c` is accepting for `M` iff its state is `M.qAccept`. -/
def PTM.isAcceptConfig (M : PTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration `c` is rejecting for `M` iff its state is `M.qReject`. -/
def PTM.isRejectConfig (M : PTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- `M` accepts input `w` along the coin-flip branch `coins` of length `n`. -/
def PTM.acceptsWithCoins (M : PTM Q Γ) (w : List Γ) (n : ℕ)
    (coins : Fin n → Bool) : Prop :=
  M.isAcceptConfig (M.runWithCoins w n coins)

/-- `M` rejects input `w` along the coin-flip branch `coins` of length `n`. -/
def PTM.rejectsWithCoins (M : PTM Q Γ) (w : List Γ) (n : ℕ)
    (coins : Fin n → Bool) : Prop :=
  M.isRejectConfig (M.runWithCoins w n coins)

/-- Decidability of acceptance along a fixed coin-flip branch, used to count
accepting branches via `Finset.filter`. -/
instance (M : PTM Q Γ) (w : List Γ) (n : ℕ) (coins : Fin n → Bool) :
    Decidable (M.acceptsWithCoins w n coins) :=
  inferInstanceAs (Decidable ((M.runWithCoins w n coins).state = M.qAccept))

/-- Decidability of rejection along a fixed coin-flip branch. -/
instance (M : PTM Q Γ) (w : List Γ) (n : ℕ) (coins : Fin n → Bool) :
    Decidable (M.rejectsWithCoins w n coins) :=
  inferInstanceAs (Decidable ((M.runWithCoins w n coins).state = M.qReject))

/-- The number of length-`n` coin-flip sequences on which `M` accepts `w`. -/
def PTM.numAccepting (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (coins : Fin n → Bool) =>
    M.acceptsWithCoins w n coins))

/-- The number of length-`n` coin-flip sequences on which `M` rejects `w`. -/
def PTM.numRejecting (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (coins : Fin n → Bool) =>
    M.rejectsWithCoins w n coins))

/-- The probability that `M` accepts `w` when run for `n` steps with uniform
random coins: `numAccepting / 2^n`. -/
def PTM.acceptProb (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℚ :=
  (M.numAccepting w n : ℚ) / ((2 : ℚ) ^ n)

/-- The probability that `M` rejects `w` when run for `n` steps with uniform
random coins: `numRejecting / 2^n`. -/
def PTM.rejectProb (M : PTM Q Γ) (w : List Γ) (n : ℕ) : ℚ :=
  (M.numRejecting w n : ℚ) / ((2 : ℚ) ^ n)

/-- `M` decides the language `A` with error at most `ε` using `t (|w|)` coin
flips on input `w`: if `w ∈ A` then `M` rejects `w` with probability `≤ ε`, and
if `w ∉ A` then `M` accepts `w` with probability `≤ ε`. -/
def PTM.decidesWithError (M : PTM Q Γ) (A : Set (List Γ)) (ε : ℚ) (t : ℕ → ℕ) : Prop :=
  (0 ≤ ε) ∧
  (∀ w : List Γ, w ∈ A → M.rejectProb w (t w.length) ≤ ε) ∧
  (∀ w : List Γ, w ∉ A → M.acceptProb w (t w.length) ≤ ε)

/-- `M` runs in time `t`: on every input `w` and every coin sequence of length
`t (|w|)`, the resulting configuration is either accepting or rejecting (i.e.
`M` has halted on every branch within `t (|w|)` steps). -/
def PTM.runsInTime (M : PTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ, ∀ coins : Fin (t w.length) → Bool,
    M.isAcceptConfig (M.runWithCoins w (t w.length) coins) ∨
    M.isRejectConfig (M.runWithCoins w (t w.length) coins)

/-- `M` is polynomial-time: there exist `k` and a runtime bound `t'` with `t'(n) = O(n^k)`
such that `M` halts on every coin-flip branch within `t'(|w|)` steps. -/
def PTM.isPolyTime (M : PTM Q Γ) : Prop :=
  ∃ (k : ℕ) (t' : ℕ → ℕ), M.runsInTime t' ∧ IsBigO t' (fun n => n ^ k)

/-- The complexity class `BPP`: `A ∈ BPP` iff some polynomial-time PTM decides
`A` with two-sided error `ε = 1/3`. -/
def InBPP {Γ : Type} [DecidableEq Γ] (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : PTM Q Γ) (k : ℕ) (t' : ℕ → ℕ),
    M.runsInTime t' ∧
    IsBigO t' (fun n => n ^ k) ∧
    M.decidesWithError A (1 / 3 : ℚ) t'

/-- An abstract "random decider" over alphabet `Γ`: given input `w` and a
sequence of `numBits w.length` random bits it returns a Boolean answer. Used as
an extensional model of a randomized algorithm. -/
structure RandomDecider (Γ : Type) [DecidableEq Γ] where
  numBits : ℕ → ℕ
  decide : (w : List Γ) → (Fin (numBits w.length) → Bool) → Bool

/-- A `RandomDecider` decides `A` with two-sided error `≤ 1/3`: for `w ∈ A` the
fraction of random strings on which it answers `false` is at most `1/3`, and
symmetrically for `w ∉ A`. -/
def RandomDecider.decidesWithBoundedError {Γ : Type} [DecidableEq Γ]
    (rd : RandomDecider Γ) (A : Set (List Γ)) : Prop :=
  (∀ w : List Γ, w ∈ A →
    ((Finset.univ.filter (fun r : Fin (rd.numBits w.length) → Bool =>
        rd.decide w r = false)).card : ℚ) / (2 : ℚ) ^ rd.numBits w.length ≤ 1 / 3) ∧
  (∀ w : List Γ, w ∉ A →
    ((Finset.univ.filter (fun r : Fin (rd.numBits w.length) → Bool =>
        rd.decide w r = true)).card : ℚ) / (2 : ℚ) ^ rd.numBits w.length ≤ 1 / 3)

/-- A `RandomDecider` is polynomial-time if its number of random bits is
polynomially bounded in the input length. -/
def RandomDecider.isPolyTime {Γ : Type} [DecidableEq Γ]
    (rd : RandomDecider Γ) : Prop :=
  ∃ k : ℕ, IsBigO rd.numBits (fun n => n ^ k)


end TuringMachine
