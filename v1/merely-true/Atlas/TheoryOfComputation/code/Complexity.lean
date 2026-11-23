/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.TuringMachines
import Atlas.TheoryOfComputation.code.NondeterministicTM
import Atlas.TheoryOfComputation.code.Reductions
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
namespace TuringMachine

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- A single nondeterministic step of `M`: `c₂` is a possible successor of `c₁`,
selected from the set of transitions `δ c₁.state (read symbol)`. Halting
configurations are fixed points. -/
def NTM.step (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  if c₁.state = M.qAccept ∨ c₁.state = M.qReject then c₂ = c₁
  else
    ∃ q' b d, (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) ∧
      let newHeadPos := match d with
        | Direction.L => c₁.headPos - 1
        | Direction.R => c₁.headPos + 1
      c₂ = ⟨q', newHeadPos, Function.update c₁.tape c₁.headPos b⟩

/-- NTM acceptance: `M` accepts `w` iff there is some finite computation branch
of length `n + 1` starting from `M.initConfig w`, with each step a valid
nondeterministic transition, ending in an accepting configuration. -/
def NTM.accepts (M : NTM Q Γ) (w : List Γ) : Prop :=
  ∃ (n : ℕ) (branch : Fin (n + 1) → Config Q Γ),
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w ∧
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) ∧
    M.isAcceptConfig (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- The language recognized by NTM `M`: the set of strings it accepts. -/
def NTM.language (M : NTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- An NTM is a decider if every computation branch on every input halts in
finitely many steps. -/
def NTM.isDecider (M : NTM Q Γ) : Prop :=
  ∀ w : List Γ, ∀ (n : ℕ) (branch : Fin (n + 1) → Config Q Γ),
    0 < n →
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w →
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) →
    ∃ k : Fin (n + 1), M.isHaltConfig (branch k)

/-- `M` decides `A` iff it is a decider and its language equals `A`. -/
def NTM.decides (M : NTM Q Γ) (A : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = A

/-- A deterministic TM runs in time `t` if it halts on every input `w` within
`t (|w|)` steps. -/
def TM.runsInTime (M : TM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ, M.isHaltConfig (M.runOnInput w (t w.length))

/-- An NTM runs in time `t` if every branch of length at most `t (|w|)` reaches
a halting configuration on input `w`. -/
def NTM.runsInTime (M : NTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    ∀ (k : ℕ) (branch : Fin (k + 1) → Config Q Γ),
      0 < k →
      branch ⟨0, Nat.zero_lt_succ k⟩ = M.initConfig w →
      (∀ (i : Fin k), M.step (branch i.castSucc) (branch i.succ)) →
      k ≤ t w.length →
      M.isHaltConfig (branch ⟨k, Nat.lt_succ_of_le le_rfl⟩)

/-- `f = O(g)`: there exist constants `c > 0` and `n₀` such that `f n ≤ c · g n`
for all `n ≥ n₀`. -/
def IsBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c n₀ : ℕ, 0 < c ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n

/-- `A ∈ TIME(t)`: some deterministic TM decides `A` in time `O(t)`. -/
def InTIME (t : ℕ → ℕ) {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ) (t' : ℕ → ℕ),
    M.decides A ∧ M.runsInTime t' ∧ IsBigO t' t

/-- `A ∈ NTIME(t)`: some nondeterministic TM decides `A` in time `O(t)`. -/
def InNTIME (t : ℕ → ℕ) {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q Γ) (t' : ℕ → ℕ),
    M.decides A ∧ M.runsInTime t' ∧ IsBigO t' t

/-- The complexity class P: `A ∈ P` iff `A ∈ TIME(n^k)` for some `k`. -/
def InP {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InTIME (fun n => n ^ k) A

/-- The complexity class NP: `A ∈ NP` iff `A ∈ NTIME(n^k)` for some `k`. -/
def InNP {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InNTIME (fun n => n ^ k) A

/-- The complexity class EXPTIME: deciders running in time `2^{n^k}` for some `k`. -/
def InEXPTIME {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InTIME (fun n => 2 ^ (n ^ k)) A

/-- A function `f : Σ* → Σ*` is polynomial-time computable: there exists a
deterministic TM `F` that, on input `w`, halts within `|w|^k` steps with `f w`
written on the prefix of its tape. -/
def IsPolyTimeComputableFunction {Γ : Type} (f : List Γ → List Γ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (F : TM Q Γ) (k : ℕ),
    (∀ w : List Γ, ∃ n : ℕ,
      n ≤ (fun m => m ^ k) w.length ∧
      F.isHaltConfig (F.runOnInput w n) ∧
      Config.readTape (F.runOnInput w n) (f w).length = f w)

/-- Polynomial-time mapping reducibility `A ≤ₚ B`: there is a polynomial-time
computable `f` with `w ∈ A ↔ f w ∈ B`. -/
def PolyReducible {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ f : List Γ → List Γ,
    IsPolyTimeComputableFunction f ∧
    ∀ w : List Γ, w ∈ A ↔ f w ∈ B

/-- Notation `A ≤ₚ B` for polynomial-time mapping reducibility. -/
scoped infixl:50 " ≤ₚ " => PolyReducible

/-- The complexity class coNP: `A ∈ coNP` iff `Aᶜ ∈ NP`. -/
def InCoNP {Γ : Type} (A : Set (List Γ)) : Prop :=
  InNP Aᶜ

/-- `O(·)` is transitive: if `f = O(g)` and `g = O(h)` then `f = O(h)`. -/
lemma IsBigO.trans {f g h : ℕ → ℕ} (hfg : IsBigO f g) (hgh : IsBigO g h) : IsBigO f h := by
  obtain ⟨c₁, n₁, hc₁, hfg⟩ := hfg
  obtain ⟨c₂, n₂, hc₂, hgh⟩ := hgh
  refine ⟨c₁ * c₂, max n₁ n₂, Nat.mul_pos hc₁ hc₂, fun n hn => ?_⟩
  have h1 := hfg n (le_of_max_le_left hn)
  have h2 := hgh n (le_of_max_le_right hn)
  calc f n ≤ c₁ * g n := h1
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left c₁ h2
    _ = c₁ * c₂ * h n := by rw [Nat.mul_assoc]

/-- Sequential composition of TMs: run `F` to completion, then transfer control
to `M_B`, finally collapsing `M_B`'s accept/reject states to fresh accept/reject
states of the composed machine. Used to reduce one decision problem to another. -/
noncomputable def composedTM
    {Γ : Type} {Q_F Q_B : Type} [DecidableEq Q_F] [DecidableEq Q_B]
    (F : TM Q_F Γ) (M_B : TM Q_B Γ) : TM ((Q_F ⊕ Q_B) ⊕ Fin 2) Γ where
  blank := F.blank
  inputAlpha := F.inputAlpha
  blank_not_in_inputAlpha := F.blank_not_in_inputAlpha
  δ := fun q γ => match q with
    | .inl (.inl q_F) =>
      if q_F = F.qAccept ∨ q_F = F.qReject then
        (.inl (.inr M_B.q₀), γ, Direction.R)
      else
        let (q', b, d) := F.δ q_F γ
        (.inl (.inl q'), b, d)
    | .inl (.inr q_B) =>
      if q_B = M_B.qAccept then
        (.inr ⟨0, by omega⟩, γ, Direction.R)
      else if q_B = M_B.qReject then
        (.inr ⟨1, by omega⟩, γ, Direction.R)
      else
        let (q', b, d) := M_B.δ q_B γ
        (.inl (.inr q'), b, d)
    | .inr n => (.inr n, γ, Direction.R)
  q₀ := .inl (.inl F.q₀)
  qAccept := .inr ⟨0, by omega⟩
  qReject := .inr ⟨1, by omega⟩
  qReject_ne_qAccept := by simp




/-- `B` is NP-hard: every `A ∈ NP` polynomial-time reduces to `B`. -/
protected def IsNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InNP A → PolyReducible A B

/-- `B` is NP-complete: `B ∈ NP` and `B` is NP-hard. -/
protected def IsNPComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InNP B ∧ TuringMachine.IsNPHard B

end TuringMachine
