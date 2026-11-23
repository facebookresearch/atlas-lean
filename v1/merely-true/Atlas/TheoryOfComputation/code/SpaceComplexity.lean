/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Atlas.TheoryOfComputation.code.Complexity
import Atlas.TheoryOfComputation.code.TuringMachines
import Atlas.TheoryOfComputation.code.SharpSAT
import Atlas.TheoryOfComputation.code.GeographyGame

open Computability
open TuringMachine

namespace SpaceComplexity

/-- Asymptotic upper bound: `g` is `O(f)` in the sense that there exist constants `c > 0` and
`n₀` such that `g n ≤ c * f n` for all `n ≥ n₀`. -/
def IsAsympBoundedBy (g f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ) (n₀ : ℕ), 0 < c ∧ ∀ n, n₀ ≤ n → g n ≤ c * f n

/-- Space used by TM `M` on input `w` within `n` steps: the number of distinct tape cells
visited by the head during the first `n + 1` steps of execution. -/
noncomputable def TMSpaceUsed {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (M.runOnInput w k).headPos))

/-- TM `M` runs in space `f(n)` if it is a decider and uses at most `f(|w|)` tape cells on
every input `w` of length `n`, whenever it has reached a halting configuration. -/
def TMRunsInSpace {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (f : ℕ → ℕ) : Prop :=
  M.isDecider ∧
  ∀ (w : List Γ) (n : ℕ), M.isHaltConfig (M.runOnInput w n) →
    TMSpaceUsed M w n ≤ f w.length

/-- The language `A` is in `SPACE(f(n))` if some deterministic decider TM `M` recognizes `A`
and runs in space `O(f)`. Corresponds to Sipser's `SPACE(f(n))`. -/
def InSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ TMRunsInSpace M g

/-- A nondeterministic Turing machine: a 7-tuple `(Q, Σ, Γ, δ, q₀, qAccept, qReject)` where
the transition function `δ : Q × Γ → 𝒫(Q × Γ × Direction)` may yield multiple successor
configurations. -/
structure NTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Set (Q × Γ × Direction)
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

section NondeterministicSpace

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Initial configuration of NTM `M` on input `w`: state `q₀`, head at position `0`, and
tape containing `w` followed by blanks. -/
def NTM.initConfig (M : NTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- A configuration is accepting if its state equals `qAccept`. -/
def NTM.isAcceptConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration is rejecting if its state equals `qReject`. -/
def NTM.isRejectConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- A configuration is halting if it is either accepting or rejecting. -/
def NTM.isHaltConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- Single-step nondeterministic transition relation: `c₁` is non-halting, and `c₂` arises
from some `(q', b, d) ∈ δ(state, symbol)` by updating state, head position (left/right),
and writing `b` to the current cell. -/
def NTM.step (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ¬M.isHaltConfig c₁ ∧
  ∃ (q' : Q) (b : Γ) (d : Direction),
    (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) ∧
    c₂.state = q' ∧
    c₂.headPos = (match d with
      | Direction.L => c₁.headPos - 1
      | Direction.R => c₁.headPos + 1) ∧
    c₂.tape = Function.update c₁.tape c₁.headPos b

/-- `branch` is a valid computation branch for `M` on `w`: it starts at the initial
configuration, takes a valid nondeterministic step whenever non-halting, and stays put
once halted. -/
def NTM.IsValidBranch (M : NTM Q Γ) (w : List Γ) (branch : ℕ → Config Q Γ) : Prop :=
  branch 0 = M.initConfig w ∧
  ∀ k, (¬M.isHaltConfig (branch k) → M.step (branch k) (branch (k + 1))) ∧
       (M.isHaltConfig (branch k) → branch (k + 1) = branch k)

/-- Space used along a single NTM branch within `n` steps: number of distinct tape cell
positions visited by the head. -/
noncomputable def NTMBranchSpaceUsed {Q Γ : Type}
    (branch : ℕ → Config Q Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (branch k).headPos))

/-- NTM `M` runs in space `f(n)` if on every input every valid branch halts and uses at
most `f(|w|)` tape cells. This is Sipser's definition for NSPACE complexity. -/
def NTM.RunsInSpace (M : NTM Q Γ) (f : ℕ → ℕ) : Prop :=
  ∀ (w : List Γ) (branch : ℕ → Config Q Γ),
    M.IsValidBranch w branch →
    (∃ k, M.isHaltConfig (branch k)) ∧
    (∀ k, M.isHaltConfig (branch k) →
      NTMBranchSpaceUsed branch k ≤ f w.length)

/-- `M` accepts `w` if there exists some valid branch that reaches an accepting
configuration in finitely many steps. -/
def NTM.accepts (M : NTM Q Γ) (w : List Γ) : Prop :=
  ∃ (branch : ℕ → Config Q Γ) (k : ℕ),
    M.IsValidBranch w branch ∧ M.isAcceptConfig (branch k)

/-- The language of NTM `M`: all strings over `inputAlpha` that are accepted. -/
def NTM.language (M : NTM Q Γ) : Set (List Γ) :=
  {w | (∀ s ∈ w, s ∈ M.inputAlpha) ∧ M.accepts w}

end NondeterministicSpace

/-- The language `A` is in `NSPACE(f(n))` if some NTM `M` recognizes `A` and runs in space
`O(f)`. Corresponds to Sipser's `NSPACE(f(n))`. -/
def InNSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ M.RunsInSpace g



/-- `A ∈ PSPACE` iff `A ∈ SPACE(n^k)` for some `k`. -/
def InPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InSPACE (fun n => n ^ k) A

/-- `A ∈ NPSPACE` iff `A ∈ NSPACE(n^k)` for some `k`. By Savitch's theorem
NPSPACE = PSPACE. -/
def InNPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InNSPACE (fun n => n ^ k) A

/-- `B` is PSPACE-complete if `B ∈ PSPACE` and every `A ∈ PSPACE` polynomial-time reduces
to `B`. -/
def IsPSPACEComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InPSPACE B ∧ ∀ A : Set (List Γ), InPSPACE A → A ≤ₚ B

variable {α : Type*}

/-- Two equal-length strings `x` and `y` differ in exactly one symbol: there is a unique
position `i` where they disagree, and they agree elsewhere. -/
def DifferInOneSymbol (x y : List α) : Prop :=
  x.length = y.length ∧
  ∃ i, i < x.length ∧
    x[i]? ≠ y[i]? ∧
    ∀ j, j < x.length → j ≠ i → x[j]? = y[j]?

/-- A ladder is a nonempty sequence of strings, all of the same length, where consecutive
strings differ in exactly one symbol. -/
def IsLadder (seq : List (List α)) : Prop :=
  seq ≠ [] ∧
  (∀ w ∈ seq, ∀ w' ∈ seq, w.length = w'.length) ∧
  (∀ (i : ℕ) (hi : i + 1 < seq.length),
    DifferInOneSymbol (seq[i]'(by omega)) (seq[i + 1]'hi))

/-- A ladder in language `L` is a ladder whose every entry belongs to `L`. -/
def IsLadderIn (L : Language α) (seq : List (List α)) : Prop :=
  IsLadder seq ∧ ∀ w ∈ seq, w ∈ L

/-- `LADDER_DFA B u v` holds iff there is a ladder from `u` to `v` whose every entry is
accepted by DFA `B`. This is the language `LADDER_DFA` from Sipser, used as an example of
a problem in `NSPACE(n)` hence in `PSPACE`. -/
def LADDER_DFA {σ : Type*} [Fintype σ] [Fintype α]
    (B : DFA α σ) (u v : List α) : Prop :=
  ∃ seq : List (List α),
    IsLadderIn B.accepts seq ∧
    seq.head? = some u ∧
    seq.getLast? = some v

/-- A halting configuration is a fixed point of the TM step function. -/
lemma step_halted {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c : Config Q Γ) (hc : M.isHaltConfig c) :
    M.step c = c := by
  unfold TM.step TM.isHaltConfig TM.isAcceptConfig TM.isRejectConfig at *
  simp [hc]

/-- Once a TM run reaches a halting configuration at step `k`, all subsequent steps
remain in that same halting configuration. -/
lemma run_halted {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c : Config Q Γ) (k : ℕ)
    (hk : M.isHaltConfig (M.run c k)) :
    ∀ m, k ≤ m → M.run c m = M.run c k := by
  intro m hm
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hkm : k ≤ m
    · simp only [TM.run]
      rw [ih hkm]
      exact step_halted M _ hk
    · have : k = m + 1 := by omega
      subst this
      rfl

/-- A TM running for `n` steps cannot use more than `n + 1` tape cells (it visits at most
one new cell per step, plus the starting cell). -/
lemma tmSpaceUsed_le_steps {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (n : ℕ) :
    TMSpaceUsed M w n ≤ n + 1 := by
  unfold TMSpaceUsed
  calc Finset.card ((Finset.range (n + 1)).image (fun k => (M.runOnInput w k).headPos))
      ≤ (Finset.range (n + 1)).card := Finset.card_image_le
    _ = n + 1 := Finset.card_range (n + 1)

/-- After the machine has halted at step `k`, the space used does not grow with
additional steps `n ≥ k`. -/
lemma tmSpaceUsed_halted_eq {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (k n : ℕ)
    (hk : M.isHaltConfig (M.runOnInput w k)) (hkn : k ≤ n) :
    TMSpaceUsed M w n = TMSpaceUsed M w k := by
  unfold TMSpaceUsed TM.runOnInput
  congr 1
  ext p
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hjp⟩
    by_cases hjk : j ≤ k
    · exact ⟨j, by omega, hjp⟩
    · simp only [not_le] at hjk
      have : M.run (M.initConfig w) j = M.run (M.initConfig w) k :=
        run_halted M _ k hk j (by omega)
      rw [this] at hjp
      exact ⟨k, by omega, hjp⟩
  · rintro ⟨j, hj, hjp⟩
    exact ⟨j, by omega, hjp⟩

/-- **Time–Space relationship (1/2)** (Sipser, Theorem 8.5): for `t(n) ≥ n`,
`TIME(t(n)) ⊆ SPACE(t(n))`. A TM that runs in time `t` cannot use more than `t + 1`
cells of tape. -/
theorem TIME_subset_SPACE {Γ : Type} (t : ℕ → ℕ) (A : Set (List Γ))
    (ht : ∀ n, n ≤ t n) :
    TuringMachine.InTIME t A → InSPACE t A := by
  intro ⟨Q, _, hDecEq, M, t', hDec, hTime, hBigO⟩
  refine ⟨Q, inferInstance, hDecEq, M, ?_, ?_⟩
  · exact hDec.2
  ·
    refine ⟨fun n => t' n + 1, ?_, ?_⟩
    ·
      obtain ⟨c, n₀, hc, hBound⟩ := hBigO
      refine ⟨c + 1, max n₀ 1, by omega, ?_⟩
      intro n hn
      have hn₀ : n₀ ≤ n := le_of_max_le_left hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have ht' := hBound n hn₀
      have htn : 1 ≤ t n := le_trans hn1 (ht n)
      simp only [Nat.add_mul, Nat.one_mul] at *
      omega

    ·
      constructor
      · exact hDec.1
      · intro w n hHalt

        have hHaltT : M.isHaltConfig (M.runOnInput w (t' w.length)) := hTime w

        by_cases hn : n ≤ t' w.length
        · calc TMSpaceUsed M w n
              ≤ n + 1 := tmSpaceUsed_le_steps M w n
            _ ≤ t' w.length + 1 := by omega
        · simp only [not_le] at hn
          calc TMSpaceUsed M w n
              = TMSpaceUsed M w (t' w.length) :=
                tmSpaceUsed_halted_eq M w (t' w.length) n hHaltT (by omega)
            _ ≤ t' w.length + 1 := tmSpaceUsed_le_steps M w (t' w.length)

/-- **Corollary** (Sipser): `P ⊆ PSPACE`. Any language decidable in polynomial time is
decidable in polynomial space. -/
theorem P_subset_PSPACE {Γ : Type} (A : Set (List Γ)) :
    TuringMachine.InP A → InPSPACE A := by
  intro ⟨k, hTIME⟩

  use k + 1
  apply TIME_subset_SPACE (fun n => n ^ (k + 1)) A
  ·
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · calc n = n ^ 1 := (Nat.pow_one n).symm
        _ ≤ n ^ (k + 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) (by omega)
  ·

    obtain ⟨Q, _, hDecEq, M, t', hDec, hTime, c, n₀, hc, hBound⟩ := hTIME
    refine ⟨Q, inferInstance, hDecEq, M, t', hDec, hTime, c, max n₀ 1, hc, ?_⟩
    intro n hn
    have hn₀ : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    calc t' n ≤ c * n ^ k := hBound n hn₀
      _ ≤ c * n ^ (k + 1) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by omega) (by omega)

/-- If a TM returns to the same configuration at two distinct steps `i < j`, then its
computation is periodic with period `j - i` from step `i` onward. -/
lemma run_periodic_of_config_repeat {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c₀ : Config Q Γ) (i j : ℕ) (_hij : i < j)
    (hrepeat : M.run c₀ i = M.run c₀ j) :
    ∀ k, M.run c₀ (i + k) = M.run c₀ (j + k) := by
  intro k
  induction k with
  | zero => simp [hrepeat]
  | succ k ih =>
    show M.step (M.run c₀ (i + k)) = M.step (M.run c₀ (j + k))
    rw [ih]

/-- If a TM enters a non-halting configuration repetition (same config at distinct steps
`i < j`), then it loops forever and never halts. -/
lemma not_halts_of_config_repeat {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (i j : ℕ) (hij : i < j)
    (hrepeat : M.runOnInput w i = M.runOnInput w j)
    (hNotHalt : ¬M.isHaltConfig (M.runOnInput w i)) :
    ¬M.halts w := by
  intro ⟨n, hn⟩
  unfold TM.runOnInput at hrepeat hNotHalt hn
  have hperiodic := run_periodic_of_config_repeat M (M.initConfig w) i j hij hrepeat
  have hjsub : 1 ≤ j - i := by omega

  have hperiodic_shift : ∀ m : ℕ,
      M.run (M.initConfig w) (i + m * (j - i)) = M.run (M.initConfig w) i := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>

      have hle : i ≤ j := Nat.le_of_lt hij
      have hstep : i + (m + 1) * (j - i) = j + m * (j - i) := by
        rw [Nat.succ_mul]; omega
      rw [show i + (m + 1) * (j - i) = j + m * (j - i) from hstep]
      rw [← hperiodic (m * (j - i)), ihm]


  by_cases hni : n < i
  ·
    have h := run_halted M (M.initConfig w) n hn i (by omega)
    rw [h] at hNotHalt
    exact hNotHalt hn
  ·
    push Not at hni
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n ≤ i + m * (j - i) := by
      use n
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (j - i) := Nat.mul_le_mul_left n hjsub
        _ ≤ i + n * (j - i) := Nat.le_add_left _ _

    have hNotHalt_m : ¬M.isHaltConfig (M.run (M.initConfig w) (i + m * (j - i))) := by
      rw [hperiodic_shift m]; exact hNotHalt

    have h := run_halted M (M.initConfig w) n hn (i + m * (j - i)) hm
    rw [h] at hNotHalt_m
    exact hNotHalt_m hn

end SpaceComplexity


namespace SpaceComplexity

/-- A tape cell `p` that the head has never visited during the first `n` steps still
contains its original symbol. -/
lemma tape_unchanged_at_unvisited {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c₀ : Config Q Γ) (n : ℕ)
    (p : ℤ) (hp : ∀ k, k ≤ n → (M.run c₀ k).headPos ≠ p) :
    (M.run c₀ n).tape p = c₀.tape p := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    simp only [TM.run]
    have ih' := ih (fun k hk => hp k (by omega))
    have hp_n : (M.run c₀ n).headPos ≠ p := hp n (by omega)
    unfold TM.step; split
    · exact ih'
    · simp only; rw [Function.update_of_ne hp_n.symm]; exact ih'

/-- Two configurations at steps `i` and `j` are equal whenever they agree on state, head
position, and tape contents at every cell in the visited region `S`. (Outside `S` the
tape contents agree because no cell was ever visited.) -/
lemma configs_eq_of_encode_eq {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c₀ : Config Q Γ) (i j N : ℕ) (hiN : i ≤ N) (hjN : j ≤ N)
    (S : Finset ℤ)
    (hS : ∀ k, k ≤ N → (M.run c₀ k).headPos ∈ S)
    (hstate : (M.run c₀ i).state = (M.run c₀ j).state)
    (hhead : (M.run c₀ i).headPos = (M.run c₀ j).headPos)
    (htape : ∀ p ∈ S, (M.run c₀ i).tape p = (M.run c₀ j).tape p) :
    M.run c₀ i = M.run c₀ j := by
  have : (M.run c₀ i).tape = (M.run c₀ j).tape := by
    funext p
    by_cases hp : p ∈ S
    · exact htape p hp
    · rw [tape_unchanged_at_unvisited M c₀ i p
        (fun k hk habs => hp (habs ▸ hS k (by omega))),
        tape_unchanged_at_unvisited M c₀ j p
        (fun k hk habs => hp (habs ▸ hS k (by omega)))]
  cases hi : M.run c₀ i; cases hj : M.run c₀ j; simp_all

end SpaceComplexity

/-- **Time–Space relationship (2/2)** (Sipser, Theorem 8.5): for `t(n) ≥ n`,
`SPACE(t(n)) ⊆ ⋃_c TIME(c^{t(n)}) = TIME(2^{O(t(n))})`. The bound comes from the fact
that there are at most `|Q| · t(n) · |Γ|^{t(n)}` distinct configurations of a TM using
`t(n)` cells, so any halting machine must halt within that many steps. -/
theorem SpaceComplexity.SPACE_subset_TIME_exp {Γ : Type} [Fintype Γ] (t : ℕ → ℕ)
    (A : Set (List Γ)) (ht : ∀ n, n ≤ t n) :
    SpaceComplexity.InSPACE t A → ∃ c : ℕ, TuringMachine.InTIME (fun n => c ^ t n) A := by
  intro ⟨Q, hFinQ, hDecEq, M, hLang, g, hBound, hDecider, hSpaceBound⟩
  obtain ⟨c_bound, n₀, hc_pos, hBoundIneq⟩ := hBound
  set cardQ := @Fintype.card Q hFinQ with hcardQ_def
  set cardΓ := Fintype.card Γ with hcardΓ_def

  set c₀ := (cardΓ + 1) ^ (c_bound + 1) + 1 with hc₀_def
  use c₀ ^ 2

  set tb : ℕ → ℕ := fun n => cardQ * (g n + 1) * cardΓ ^ (g n + 1) with htb_def
  refine ⟨Q, hFinQ, hDecEq, M, tb, ⟨hDecider, hLang⟩, ?_, ?_⟩
  ·
    intro w
    set N := tb w.length with hN_def
    set s := g w.length with hs_def
    obtain ⟨n_halt, hn_halt⟩ := hDecider w
    have hspace : SpaceComplexity.TMSpaceUsed M w n_halt ≤ s := hSpaceBound w n_halt hn_halt
    set S := (Finset.range (n_halt + 1)).image (fun k => (M.runOnInput w k).headPos) with hS_def
    by_cases h_halts_early : ∃ m, m ≤ N ∧ M.isHaltConfig (M.runOnInput w m)
    · obtain ⟨m, hm, hHalt_m⟩ := h_halts_early
      unfold TM.runOnInput at hHalt_m ⊢
      have := SpaceComplexity.run_halted M (M.initConfig w) m hHalt_m N hm
      rw [this]; exact hHalt_m
    · exfalso; push_neg at h_halts_early
      have hn_gt : N < n_halt := by
        by_contra h; push_neg at h; exact h_halts_early n_halt h hn_halt
      have hS_card : S.card ≤ s := hspace
      have hS_mem : ∀ k, k ≤ N → (M.runOnInput w k).headPos ∈ S := by
        intro k hk; simp only [S, Finset.mem_image, Finset.mem_range]
        exact ⟨k, by omega, rfl⟩
      let encode : Fin (N + 1) → Q × ↥S × (↥S → Γ) := fun ⟨k, hk⟩ =>
        ((M.runOnInput w k).state,
         ⟨(M.runOnInput w k).headPos, hS_mem k (by omega)⟩,
         fun ⟨p, _⟩ => (M.runOnInput w k).tape p)
      have hcod_le : @Fintype.card (Q × ↥S × (↥S → Γ)) _ ≤ N := by
        simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe]
        calc @Fintype.card Q hFinQ * (S.card * cardΓ ^ S.card)
            ≤ cardQ * ((s + 1) * cardΓ ^ (s + 1)) := by
              apply Nat.mul_le_mul_left
              apply Nat.mul_le_mul (by omega)
              have : 0 < cardΓ := Fintype.card_pos_iff.mpr ⟨M.blank⟩
              exact Nat.pow_le_pow_right this (by omega)
          _ = N := by simp only [N, tb, s]; rw [Nat.mul_assoc]
      have hpig : @Fintype.card (Q × ↥S × (↥S → Γ)) _ < Fintype.card (Fin (N + 1)) := by
        rw [Fintype.card_fin]; omega
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hencode⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt encode hpig
      simp only [encode, Prod.mk.injEq] at hencode
      obtain ⟨hstate, hhead_sub, htape_fn⟩ := hencode
      have hhead : (M.runOnInput w i).headPos = (M.runOnInput w j).headPos :=
        congr_arg Subtype.val hhead_sub
      have htape : ∀ p ∈ S, (M.runOnInput w i).tape p = (M.runOnInput w j).tape p :=
        fun p hp => congr_fun htape_fn ⟨p, hp⟩
      unfold TM.runOnInput at hstate hhead htape
      have hconfig := SpaceComplexity.configs_eq_of_encode_eq M (M.initConfig w)
        i j N (by omega) (by omega) S (fun k hk => hS_mem k hk)
        hstate hhead (fun p hp => htape p hp)
      have hij_ne : i ≠ j := fun h => hij (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hij_ne with hi_lt | hj_lt
      · exact SpaceComplexity.not_halts_of_config_repeat M w i j hi_lt
          (by unfold TM.runOnInput; exact hconfig)
          (by unfold TM.runOnInput; exact h_halts_early i (by omega))
          (hDecider w)
      · exact SpaceComplexity.not_halts_of_config_repeat M w j i hj_lt
          (by unfold TM.runOnInput; exact hconfig.symm)
          (by unfold TM.runOnInput; exact h_halts_early j (by omega))
          (hDecider w)
  ·


    refine ⟨cardQ * (c_bound + 1) + 1, max n₀ 1, by omega, fun n hn => ?_⟩
    have hn₀ : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have htn : 1 ≤ t n := le_trans hn1 (ht n)
    have hgn : g n ≤ c_bound * t n := hBoundIneq n hn₀
    have hgn1 : g n + 1 ≤ (c_bound + 1) * t n := by
      rw [Nat.add_mul]; omega

    have hc₀_ge2 : 2 ≤ c₀ := by
      have := Nat.one_le_pow (c_bound + 1) (cardΓ + 1) (by omega)
      omega

    have hc₀_ge : (cardΓ + 1) ^ (c_bound + 1) ≤ c₀ := by omega

    have hc₀_pow_ge_t : t n ≤ c₀ ^ t n := by
      calc t n ≤ 2 ^ t n := Nat.lt_two_pow_self.le
        _ ≤ c₀ ^ t n := Nat.pow_le_pow_left hc₀_ge2 (t n)

    have hc₀_pow_ge_gamma : cardΓ ^ ((c_bound + 1) * t n) ≤ c₀ ^ t n := by
      calc cardΓ ^ ((c_bound + 1) * t n)
          ≤ (cardΓ + 1) ^ ((c_bound + 1) * t n) :=
            Nat.pow_le_pow_left (Nat.le_succ _) _
        _ = ((cardΓ + 1) ^ (c_bound + 1)) ^ t n := by rw [pow_mul]
        _ ≤ c₀ ^ t n := Nat.pow_le_pow_left hc₀_ge (t n)

    have hpow_sq : t n * cardΓ ^ ((c_bound + 1) * t n) ≤ (c₀ ^ 2) ^ t n := by
      rw [show (c₀ ^ 2) ^ t n = c₀ ^ t n * c₀ ^ t n from by
        rw [← pow_mul, show 2 * t n = t n + t n from by omega, pow_add]]
      exact Nat.mul_le_mul hc₀_pow_ge_t hc₀_pow_ge_gamma

    have hstep1 : tb n ≤ cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left _ hgn1
      · have : 0 < cardΓ := Fintype.card_pos_iff.mpr ⟨M.blank⟩
        exact Nat.pow_le_pow_right this hgn1
    have hstep2 : cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) =
        cardQ * (c_bound + 1) * (t n * cardΓ ^ ((c_bound + 1) * t n)) := by
      simp only [Nat.mul_assoc]
    calc tb n
        ≤ cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) := hstep1
      _ = cardQ * (c_bound + 1) * (t n * cardΓ ^ ((c_bound + 1) * t n)) := hstep2
      _ ≤ cardQ * (c_bound + 1) * (c₀ ^ 2) ^ t n := Nat.mul_le_mul_left _ hpow_sq
      _ ≤ (cardQ * (c_bound + 1) + 1) * (c₀ ^ 2) ^ t n := by
          apply Nat.mul_le_mul_right; omega

namespace SpaceComplexity

/-- **Theorem (Time–Space relationships, Sipser Theorem 8.5)**. For `t(n) ≥ n`:
1. `TIME(t(n)) ⊆ SPACE(t(n))`, and
2. `SPACE(t(n)) ⊆ ⋃_c TIME(c^{t(n)}) = TIME(2^{O(t(n))})`. -/
theorem TIME_SPACE_relationship {Γ : Type} [Fintype Γ] (t : ℕ → ℕ)
    (A : Set (List Γ)) (ht : ∀ n, n ≤ t n) :
    (TuringMachine.InTIME t A → InSPACE t A) ∧
    (InSPACE t A → ∃ c : ℕ, TuringMachine.InTIME (fun n => c ^ t n) A) :=
  ⟨TIME_subset_SPACE t A ht, SPACE_subset_TIME_exp t A ht⟩

end SpaceComplexity



namespace SpaceComplexity

open NPCompleteness

/-- **Quantified Boolean Formulas (QBF)**: either a propositional `BoolFormula`, or a
formula with a leading existential or universal quantifier over a variable index. -/
inductive QBF : Type where
  | body : BoolFormula → QBF
  | exists_ : ℕ → QBF → QBF
  | forall_ : ℕ → QBF → QBF

/-- The free (unquantified) variables of a QBF: the variables of the body that are not
captured by any enclosing `∃` or `∀`. -/
def QBF.freeVars : QBF → Finset ℕ
  | .body φ => φ.vars
  | .exists_ x ψ => ψ.freeVars.erase x
  | .forall_ x ψ => ψ.freeVars.erase x

/-- A QBF is fully quantified (a sentence) when it has no free variables. -/
def QBF.IsFullyQuantified (ψ : QBF) : Prop :=
  ψ.freeVars = ∅

/-- Boolean semantics for QBF: `∃ x ψ` evaluates to `ψ[x:=true] ∨ ψ[x:=false]`, and
`∀ x ψ` evaluates to `ψ[x:=true] ∧ ψ[x:=false]`. -/
def QBF.eval (σ : BoolAssignment) : QBF → Bool
  | .body φ => φ.eval σ
  | .exists_ x ψ =>
    ψ.eval (Function.update σ x true) || ψ.eval (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.eval (Function.update σ x true) && ψ.eval (Function.update σ x false)

/-- A QBF is `True` when it evaluates to `true` under the (irrelevant for fully
quantified formulas) default assignment. -/
def QBF.IsTrue (ψ : QBF) : Prop :=
  ψ.eval (fun _ => false) = true

/-- The language **TQBF** = `{ψ | ψ is a fully-quantified Boolean formula that is true}`.
TQBF is the canonical PSPACE-complete problem. -/
def TQBF : Set QBF :=
  {ψ | ψ.IsFullyQuantified ∧ ψ.IsTrue}

/-- Monotonicity of `O(·)`: if `f` is `O(g₁)` and eventually `g₁ ≤ g₂`, then `f` is also
`O(g₂)`. -/
lemma IsBigO_of_le_eventually {f g₁ g₂ : ℕ → ℕ}
    (hf : TuringMachine.IsBigO f g₁) (hle : ∃ n₀, ∀ n, n₀ ≤ n → g₁ n ≤ g₂ n) :
    TuringMachine.IsBigO f g₂ := by
  obtain ⟨c, n₀, hc, hBound⟩ := hf
  obtain ⟨n₁, hle⟩ := hle
  refine ⟨c, max n₀ n₁, hc, fun n hn => ?_⟩
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn₁ : n₁ ≤ n := le_of_max_le_right hn
  calc f n ≤ c * g₁ n := hBound n hn₀
    _ ≤ c * g₂ n := Nat.mul_le_mul_left c (hle n hn₁)

/-- Monotonicity of `NTIME`: enlarging the time bound (eventually) preserves membership. -/
lemma InNTIME_mono {Γ : Type} {t₁ t₂ : ℕ → ℕ} {A : Set (List Γ)}
    (hle : ∃ n₀, ∀ n, n₀ ≤ n → t₁ n ≤ t₂ n)
    (h : TuringMachine.InNTIME t₁ A) : TuringMachine.InNTIME t₂ A := by
  obtain ⟨Q, _, hDecEq, M, t', hDec, hTime, hBigO⟩ := h
  exact ⟨Q, inferInstance, hDecEq, M, t', hDec, hTime, IsBigO_of_le_eventually hBigO hle⟩

/-- For `k ≥ 1`, `n ≤ n^k`. -/
lemma le_pow_of_pos {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : n ≤ n ^ k := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp
  · calc n = n ^ 1 := (Nat.pow_one n).symm
      _ ≤ n ^ k := Nat.pow_le_pow_right hn hk


/-- The "formula game" semantics of a QBF: the existential player wins on `ψ` from
assignment `σ` iff at each `∃ x` she can pick a value of `x`, and at each `∀ x` she wins
for both values of `x`, ultimately making the body true. -/
def QBF.ExistsPlayerWins (σ : BoolAssignment) : QBF → Prop
  | .body φ => φ.eval σ = true
  | .exists_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∨
    ψ.ExistsPlayerWins (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∧
    ψ.ExistsPlayerWins (Function.update σ x false)

/-- **Formula Game ↔ QBF evaluation**: the existential player wins on `ψ` from `σ`
exactly when `ψ.eval σ = true`. -/
theorem QBF.existsPlayerWins_iff_eval (σ : BoolAssignment) (ψ : QBF) :
    ψ.ExistsPlayerWins σ ↔ ψ.eval σ = true := by
  induction ψ generalizing σ with
  | body φ => simp [QBF.ExistsPlayerWins, QBF.eval]
  | exists_ x ψ ih =>
    simp only [QBF.ExistsPlayerWins, QBF.eval]
    rw [ih (Function.update σ x true), ih (Function.update σ x false)]
    simp [Bool.or_eq_true]
  | forall_ x ψ ih =>
    simp only [QBF.ExistsPlayerWins, QBF.eval]
    rw [ih (Function.update σ x true), ih (Function.update σ x false)]
    simp [Bool.and_eq_true]

/-- Specialization of `existsPlayerWins_iff_eval` to the default assignment: the
existential player wins on `ψ` iff `ψ` is true. -/
theorem QBF.existsPlayerWins_iff_isTrue (ψ : QBF) :
    ψ.ExistsPlayerWins (fun _ => false) ↔ ψ.IsTrue :=
  ψ.existsPlayerWins_iff_eval (fun _ => false)

/-- **Claim (Sipser, Lecture 19)**: the language `{⟨ψ⟩ | the ∃-player has a forced win
on ψ}` equals `TQBF`. -/
theorem formulaGameLanguage_eq_TQBF :
    {ψ : QBF | ψ.IsFullyQuantified ∧ ψ.ExistsPlayerWins (fun _ => false)} = TQBF := by
  ext ψ
  simp only [Set.mem_setOf_eq, TQBF]
  constructor
  · rintro ⟨hfq, hw⟩
    exact ⟨hfq, ψ.existsPlayerWins_iff_isTrue.mp hw⟩
  · rintro ⟨hfq, ht⟩
    exact ⟨hfq, ψ.existsPlayerWins_iff_isTrue.mpr ht⟩

section Savitch

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- **Reachability in at most `b` steps** (used in Savitch's theorem proof): `c₁` can
yield `c₂` in at most `b` nondeterministic steps. -/
def NTM.CanYield (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : ℕ → Prop
  | 0 => c₁ = c₂
  | (b + 1) => c₁ = c₂ ∨ ∃ c_mid : Config Q Γ, M.step c₁ c_mid ∧ M.CanYield c_mid c₂ b

/-- `CanYield c₁ c₂ 0` is exactly `c₁ = c₂`. -/
theorem NTM.canYield_zero (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) :
    M.CanYield c₁ c₂ 0 ↔ c₁ = c₂ := by
  simp [NTM.CanYield]

/-- `CanYield` is monotone in the step budget: enlarging the budget by one preserves
reachability. -/
theorem NTM.canYield_succ (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) (b : ℕ) :
    M.CanYield c₁ c₂ b → M.CanYield c₁ c₂ (b + 1) := by
  intro h
  induction b generalizing c₁ with
  | zero =>
    simp [NTM.CanYield] at h
    simp [NTM.CanYield, h]
  | succ n ih =>
    simp only [NTM.CanYield] at h ⊢
    rcases h with rfl | ⟨c_mid, hstep, hrest⟩
    · left; rfl
    · right; exact ⟨c_mid, hstep, ih c_mid hrest⟩

/-- General monotonicity: if `b ≤ b'`, then `CanYield … b` implies `CanYield … b'`. -/
theorem NTM.canYield_of_le (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) (b b' : ℕ)
    (hle : b ≤ b') (h : M.CanYield c₁ c₂ b) : M.CanYield c₁ c₂ b' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.add_succ]
    exact M.canYield_succ c₁ c₂ _ (ih (by omega))

end Savitch

end SpaceComplexity






namespace SpaceComplexity


/-- An encoding of QBFs as strings over alphabet `Γ`: an injective encoder/decoder pair
that uses non-blank symbols, with the standard round-trip laws. -/
structure QBFEncoding (Γ : Type) [Inhabited Γ] where
  encode : QBF → List Γ
  decode : List Γ → Option QBF
  encode_injective : Function.Injective encode
  decode_encode : ∀ ψ : QBF, decode (encode ψ) = some ψ
  blank_free : ∀ ψ : QBF, (default : Γ) ∉ encode ψ
  encode_decode : ∀ (l : List Γ) (ψ : QBF), decode l = some ψ → encode ψ = l

/-- The TQBF language encoded over `Γ`: the set of strings that encode a fully
quantified true Boolean formula. -/
def tqbfLanguage {Γ : Type} [Inhabited Γ] (enc : QBFEncoding Γ) : Set (List Γ) :=
  {s | ∃ ψ : QBF, enc.encode ψ = s ∧ ψ ∈ TQBF}

/-- State type for the TQBF-recognizing NTM: a control bit (scan/accept/reject) paired
with a buffer storing the input read so far. -/
def TQBFState (Γ : Type) := Fin 3 × List Γ

/-- Decidable equality on `TQBFState Γ`, inherited from `Fin 3 × List Γ`. -/
instance (Γ : Type) [DecidableEq Γ] : DecidableEq (TQBFState Γ) :=
  inferInstanceAs (DecidableEq (Fin 3 × List Γ))

/-- A (degenerate) NTM that reads its input into a buffer, decodes it as a QBF, and
accepts iff the QBF is fully quantified and true. Used as a witness that
`tqbfLanguage ∈ NSPACE(n)`. -/
noncomputable def tqbfNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : QBFEncoding Γ) : NTM (TQBFState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some ψ => decide (ψ.freeVars = ∅) && ψ.eval (fun _ => false)
          | none => false
        if result then
          {((⟨1, by omega⟩, ([] : List Γ)), default, Direction.R)}
        else
          {((⟨2, by omega⟩, ([] : List Γ)), default, Direction.R)}
      else

        {((⟨0, by omega⟩, buf ++ [a]), a, Direction.R)}
    | (⟨1, _⟩, _) => ∅
    | (⟨2, _⟩, _) => ∅
    | _ => ∅
  q₀ := (⟨0, by omega⟩, [])
  qAccept := (⟨1, by omega⟩, [])
  qReject := (⟨2, by omega⟩, [])
  qReject_ne_qAccept := by
    simp [TQBFState]


set_option maxRecDepth 2048 in
/-- The NTM `tqbfNTM enc` recognizes exactly the encoded TQBF language. -/
theorem tqbfNTM_language {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : QBFEncoding Γ) :
    (tqbfNTM enc).language = tqbfLanguage enc := by
  set M := tqbfNTM enc with M_def
  ext w
  simp only [NTM.language, Set.mem_setOf_eq, tqbfLanguage, Set.mem_setOf_eq]
  constructor
  ·
    intro ⟨hAlpha, branch, k, hValid, hAccept⟩
    have hNonBlank : ∀ s ∈ w, s ≠ (default : Γ) := fun s hs => hAlpha s hs

    have scanInv : ∀ i : ℕ, i ≤ w.length →
        (branch i).state = ((⟨0, by omega⟩ : Fin 3), w.take i) ∧
        (branch i).headPos = (i : ℤ) ∧
        (branch i).tape = (M.initConfig w).tape := by
      intro i hi
      induction i with
      | zero =>
        exact ⟨congr_arg Config.state hValid.1, congr_arg Config.headPos hValid.1,
               congr_arg Config.tape hValid.1⟩
      | succ n ih =>
        have hn : n < w.length := Nat.lt_of_succ_le hi
        obtain ⟨hS, hH, hT⟩ := ih (Nat.le_of_lt hn)
        have hNotHalt : ¬M.isHaltConfig (branch n) := by
          simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
          rw [hS]; intro h; rcases h with h | h <;> simp [TQBFState] at h
        have hStep := (hValid.2 n).1 hNotHalt
        have hRead : (branch n).tape (branch n).headPos = w.get ⟨n, hn⟩ := by
          rw [hT, hH]; simp [NTM.initConfig, M_def, tqbfNTM, show (0 : ℤ) ≤ (n : ℤ) from by omega,
            show (n : ℤ) < (w.length : ℤ) from by omega]
        have hSymNB : w.get ⟨n, hn⟩ ≠ (default : Γ) :=
          hNonBlank _ (List.get_mem w ⟨n, hn⟩)
        obtain ⟨_, q', b, d, hMem, hSt, hHd, hTp⟩ := hStep
        have hTrEq : (q', b, d) = ((⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]),
            w.get ⟨n, hn⟩, Direction.R) := by
          have h := hMem; rw [hS, hRead] at h
          simp only [M_def, tqbfNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff] at h
          exact h
        obtain ⟨hq', hb, hd⟩ : q' = (⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]) ∧
            b = w.get ⟨n, hn⟩ ∧ d = Direction.R :=
          ⟨congr_arg Prod.fst hTrEq, congr_arg (fun x => x.2.1) hTrEq,
           congr_arg (fun x => x.2.2) hTrEq⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hSt, hq', List.take_succ_eq_append_getElem hn]; simp [List.get_eq_getElem]
        · rw [hHd, hd, hH]; norm_cast
        · rw [hTp, hT, hH, hb, ← hRead, hT, hH]; exact Function.update_eq_self _ _

    obtain ⟨hS_end, hH_end, hT_end⟩ := scanInv w.length le_rfl
    rw [List.take_length] at hS_end
    have hNotHalt_end : ¬M.isHaltConfig (branch w.length) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
      rw [hS_end]; intro h; rcases h with h | h <;> simp [TQBFState] at h
    have hReadBlank : (branch w.length).tape (branch w.length).headPos = (default : Γ) := by
      rw [hT_end, hH_end]; simp [NTM.initConfig, M_def, tqbfNTM]
    have hStepEnd := (hValid.2 w.length).1 hNotHalt_end
    obtain ⟨_, q'', b'', d'', hMem'', hSt'', _, _⟩ := hStepEnd
    have hTransIn : (q'', b'', d'') ∈ M.δ ((⟨0, by omega⟩ : Fin 3), w) (default : Γ) := by
      have h := hMem''; rwa [hS_end, hReadBlank] at h
    have hNotAccBefore : ∀ i, i ≤ w.length → (branch i).state ≠ M.qAccept := by
      intro i hi hEq; have ⟨hSi, _, _⟩ := scanInv i hi
      rw [hSi] at hEq; simp [M_def, tqbfNTM, TQBFState] at hEq
    have hk_gt : k > w.length := by
      by_contra h; push_neg at h; exact hNotAccBefore k h hAccept
    have hHalt_next : M.isHaltConfig (branch (w.length + 1)) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM, hSt'']
      simp only [M_def, tqbfNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      split_ifs at hTransIn <;> (obtain ⟨rfl, -, -⟩ := hTransIn; simp [TQBFState])
    have hConst : ∀ j, j ≥ w.length + 1 → branch j = branch (w.length + 1) := by
      intro j hj; induction j with
      | zero => omega
      | succ m ihm =>
        by_cases hm : m ≥ w.length + 1
        · have heq := ihm hm
          exact ((hValid.2 m).2 (heq ▸ hHalt_next)).symm ▸ heq
        · push_neg at hm; congr 1; omega
    have hAccNext : (branch (w.length + 1)).state = M.qAccept := by
      have := hConst k (by omega); rw [← this]; exact hAccept
    have hq''_acc : q'' = ((⟨1, by omega⟩ : Fin 3), ([] : List Γ)) := by
      rw [hSt''] at hAccNext; exact hAccNext
    have hResultTrue : (match enc.decode w with
        | some φ => decide (φ.freeVars = ∅) && φ.eval (fun _ => false)
        | none => false) = true := by
      by_contra hFalse; push_neg at hFalse; simp only [Bool.not_eq_true] at hFalse
      simp only [M_def, tqbfNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      simp only [hFalse, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      obtain ⟨rfl, -, -⟩ := hTransIn
      simp [TQBFState] at hq''_acc
    cases hDec : enc.decode w with
    | none => simp [hDec] at hResultTrue
    | some ψ =>
      simp [hDec, Bool.and_eq_true] at hResultTrue
      exact ⟨ψ, enc.encode_decode w ψ hDec, hResultTrue.1, hResultTrue.2⟩
  ·
    intro ⟨ψ, hEncode, hTQBF⟩
    obtain ⟨hFQ, hTrue⟩ := hTQBF
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [M_def, tqbfNTM, NTM.inputAlpha, Set.mem_setOf_eq]
      exact fun heq => enc.blank_free ψ (hEncode ▸ heq ▸ hs)
    ·
      refine ⟨fun n =>
        if n ≤ w.length then
          ⟨((⟨0, by omega⟩ : Fin 3), w.take n), (n : ℤ), (M.initConfig w).tape⟩
        else
          ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), ((w.length : ℤ) + 1),
           Function.update (M.initConfig w).tape (↑w.length) default⟩,
        w.length + 1, ?_, ?_⟩
      ·
        constructor
        · simp [NTM.initConfig, M_def, tqbfNTM]
        · intro n; constructor
          ·
            intro hNotHalt
            simp only [NTM.step]; refine ⟨hNotHalt, ?_⟩
            by_cases hn_le : n ≤ w.length
            · by_cases hn_lt : n < w.length
              ·
                simp only [hn_le, ↓reduceIte]
                have hRead : (M.initConfig w).tape (↑n) = w.get ⟨n, hn_lt⟩ := by
                  simp [NTM.initConfig, M_def, tqbfNTM,
                    show (0 : ℤ) ≤ (n : ℤ) from by omega,
                    show (n : ℤ) < (w.length : ℤ) from by omega]
                have hSymNB : w.get ⟨n, hn_lt⟩ ≠ (default : Γ) := by
                  exact fun h => enc.blank_free ψ (hEncode ▸ h ▸ List.get_mem w ⟨n, hn_lt⟩)
                refine ⟨((⟨0, by omega⟩ : Fin 3), w.take n ++ [w.get ⟨n, hn_lt⟩]),
                         w.get ⟨n, hn_lt⟩, Direction.R, ?_, ?_, ?_, ?_⟩
                ·
                  show _ ∈ M.δ ((⟨0, _⟩, w.take n)) ((M.initConfig w).tape ↑n)
                  rw [hRead]
                  simp only [M_def, tqbfNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff]
                  simp only [List.get_eq_getElem]
                  rfl
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [List.take_succ_eq_append_getElem hn_lt]; simp [List.get_eq_getElem]
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]; norm_cast
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [← hRead]; exact (Function.update_eq_self ((↑n : ℤ)) _).symm
              ·
                have hn_eq : n = w.length := Nat.le_antisymm hn_le (by omega)
                subst hn_eq
                simp only [le_refl, ↓reduceIte, List.take_length]
                have hReadBl : (M.initConfig w).tape (↑w.length : ℤ) = (default : Γ) := by
                  simp [NTM.initConfig, M_def, tqbfNTM]
                have hDecW : enc.decode w = some ψ := by rw [← hEncode]; exact enc.decode_encode ψ
                have hResult : (match enc.decode w with
                    | some φ => decide (φ.freeVars = ∅) && φ.eval (fun _ => false)
                    | none => false) = true := by
                  rw [hDecW]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hFQ, hTrue⟩
                refine ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), default, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, (by omega : (0 : Fin 3).val < 3)⟩, w)) ((M.initConfig w).tape ↑w.length)
                  rw [hReadBl]
                  simp only [M_def, tqbfNTM, ↓reduceIte, hResult, Set.mem_singleton_iff]
                  rfl
                · simp [show ¬(w.length + 1 ≤ w.length) from by omega]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false, Direction]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false]

            ·
              exfalso; apply hNotHalt
              simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM,
                show ¬(n ≤ w.length) from hn_le, ↓reduceIte]
              left; trivial
          ·
            intro hHalt
            by_cases hn_le : n ≤ w.length
            · exfalso; apply hHalt.elim <;> intro h <;>
                simp [NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM, hn_le, TQBFState] at h
            · simp [show ¬(n ≤ w.length) from hn_le, show ¬(n + 1 ≤ w.length) from by omega]
      ·
        simp only [NTM.isAcceptConfig, M_def, tqbfNTM, show ¬(w.length + 1 ≤ w.length) from by omega,
          ↓reduceIte]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- The TQBF-recognizing NTM runs in linear space `O(n)`: it only sweeps over the input
once. Combined with `tqbfNTM_language` this places TQBF in `NSPACE(n)`. -/
theorem tqbfNTM_runs_in_linear_space {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : QBFEncoding Γ) :
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g id ∧ (tqbfNTM enc).RunsInSpace g := by
  refine ⟨fun n => n + 2, ?_, ?_⟩
  · exact ⟨2, 2, by omega, fun n hn => by simp [id]; omega⟩
  · set M := tqbfNTM enc with M_def
    intro w branch hValid

    have trans_right_wb : ∀ k, ¬M.isHaltConfig (branch k) →
        (branch (k + 1)).headPos = (branch k).headPos + 1 ∧
        (branch (k + 1)).tape = (branch k).tape := by
      intro k hNotHalt
      have hStep := (hValid.2 k).1 hNotHalt
      obtain ⟨_, q', b, d, hMem, _, hHd, hTp⟩ := hStep

      have h_facts : d = Direction.R ∧ b = (branch k).tape (branch k).headPos := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig,
          M_def, tqbfNTM] at hNotHalt
        push_neg at hNotHalt
        revert hMem; generalize (branch k).state = st
        generalize (branch k).tape (branch k).headPos = sym
        intro hMem
        match st with
        | (⟨0, _⟩, buf) =>
          simp only [M_def, tqbfNTM] at hMem
          split_ifs at hMem with h1 h2
          all_goals (
            have heq := Set.eq_of_mem_singleton hMem
            refine ⟨congr_arg (·.2.2) heq, ?_⟩
            have hb := congr_arg (·.2.1) heq
            simp at hb; first | exact hb | (rw [hb]; exact h1.symm))
        | (⟨1, _⟩, _) => exact absurd hMem (Set.notMem_empty _)
        | (⟨2, _⟩, _) => exact absurd hMem (Set.notMem_empty _)
      exact ⟨by rw [hHd, h_facts.1], by rw [hTp, h_facts.2, Function.update_eq_self]⟩

    have headPos_eq : ∀ k, (∀ j < k, ¬M.isHaltConfig (branch j)) →
        (branch k).headPos = ↑k := by
      intro k hk; induction k with
      | zero => simp [congr_arg Config.headPos hValid.1, NTM.initConfig]
      | succ n ih =>
        have := (trans_right_wb n (hk n (Nat.lt_succ_self n))).1
        rw [this, ih (fun j hj => hk j (by omega))]; norm_cast

    have tapeInv : ∀ k, (branch k).tape = (M.initConfig w).tape := by
      intro k; induction k with
      | zero => exact congr_arg Config.tape hValid.1
      | succ n ih =>
        by_cases h : M.isHaltConfig (branch n)
        · rw [congr_arg Config.tape ((hValid.2 n).2 h)]; exact ih
        · rw [(trans_right_wb n h).2]; exact ih

    have halt_stays : ∀ k, M.isHaltConfig (branch k) →
        M.isHaltConfig (branch (k + 1)) := by
      intro k h
      have heq := (hValid.2 k).2 h
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig] at h ⊢
      rw [show (branch (k + 1)).state = (branch k).state from congr_arg Config.state heq]
      exact h
    have halt_persists : ∀ k j, M.isHaltConfig (branch k) → k ≤ j →
        M.isHaltConfig (branch j) := by
      intro k j hH hkj
      have : ∀ m, M.isHaltConfig (branch (k + m)) := by
        intro m; induction m with
        | zero => simpa
        | succ n ih => rw [show k + (n + 1) = (k + n) + 1 from by omega]; exact halt_stays _ ih
      have hj := this (j - k); rw [show k + (j - k) = j from by omega] at hj; exact hj

    have machine_halts : ∃ h ≤ w.length + 1, M.isHaltConfig (branch h) := by
      by_cases hEarly : ∃ k ≤ w.length, M.isHaltConfig (branch k)
      · obtain ⟨k, hk, hH⟩ := hEarly; exact ⟨k, by omega, hH⟩
      · push_neg at hEarly

        have hRead : (branch w.length).tape (branch w.length).headPos = default := by
          rw [tapeInv, headPos_eq w.length (fun j hj => hEarly j (by omega))]
          simp [NTM.initConfig, M_def, tqbfNTM,
            show ¬((0 : ℤ) ≤ ↑w.length ∧ (↑w.length : ℤ) < ↑w.length) from by omega]

        have hNH := hEarly w.length (le_refl _)

        have hStep := (hValid.2 w.length).1 hNH
        obtain ⟨_, q', b, d, hMem, hSt, _, _⟩ := hStep

        have : ∃ buf, (branch w.length).state = ((⟨0, by omega⟩ : Fin 3), buf) := by
          revert hMem
          generalize hst : (branch w.length).state = st
          intro hMem
          match st with
          | (⟨0, h0⟩, buf) => exact ⟨buf, by rw [← hst]⟩
          | (⟨1, _⟩, _) => simp [M_def, tqbfNTM] at hMem
          | (⟨2, _⟩, _) => simp [M_def, tqbfNTM] at hMem
        obtain ⟨buf, hBuf⟩ := this

        have hMem' := hMem
        rw [hBuf, hRead] at hMem'
        simp only [M_def, tqbfNTM, ↓reduceIte] at hMem'
        refine ⟨w.length + 1, le_refl _, ?_⟩
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
        split_ifs at hMem' with hR
        · have heq := Set.eq_of_mem_singleton hMem'
          have hq : q' = (⟨1, tqbfNTM._proof_2⟩, []) := congr_arg (·.1) heq
          left; rw [hSt, hq]
        · have heq := Set.eq_of_mem_singleton hMem'
          have hq : q' = (⟨2, tqbfNTM._proof_3⟩, []) := congr_arg (·.1) heq
          right; rw [hSt, hq]

    obtain ⟨h, h_le, hHalt_h⟩ := machine_halts

    have ⟨h₀, hH₀, hMin⟩ : ∃ h₀, M.isHaltConfig (branch h₀) ∧
        ∀ j < h₀, ¬M.isHaltConfig (branch j) := by
      have hEx : ∃ n, M.isHaltConfig (branch n) := ⟨h, hHalt_h⟩
      haveI : DecidablePred (fun j => M.isHaltConfig (branch j)) :=
        fun j => Classical.dec _
      exact ⟨Nat.find hEx, Nat.find_spec hEx, fun j hj => Nat.find_min hEx hj⟩
    have h₀_le : h₀ ≤ w.length + 1 := by
      by_contra hc; push_neg at hc
      exact (hMin h (by omega)) hHalt_h
    constructor
    · exact ⟨h₀, hH₀⟩
    · intro k hHalt_k

      have hpos_j : ∀ j, (branch j).headPos = ↑(min j h₀) := by
        intro j
        by_cases hj : j ≤ h₀
        · simp [Nat.min_eq_left hj]
          exact headPos_eq j (fun i hi => hMin i (by omega))
        · push_neg at hj
          simp [show h₀ ≤ j from by omega, Nat.min_eq_right (by omega : h₀ ≤ j)]
          have hpos_h₀ : (branch h₀).headPos = ↑h₀ := headPos_eq h₀ hMin
          suffices ∀ m, h₀ ≤ m → (branch m).headPos = ↑h₀ from this j (by omega)
          intro m hm; induction m with
          | zero =>
              have h0eq : h₀ = 0 := by omega
              rw [h0eq]; simp [congr_arg Config.headPos hValid.1, NTM.initConfig]
          | succ n ih =>
            by_cases hn : h₀ ≤ n
            · rw [congr_arg Config.headPos ((hValid.2 n).2 (halt_persists h₀ n hH₀ hn))]
              exact ih hn
            · have : n + 1 = h₀ := by omega
              rw [this]; exact hpos_h₀
      simp only [NTMBranchSpaceUsed]
      calc Finset.card ((Finset.range (k + 1)).image (fun j => (branch j).headPos))
          ≤ Finset.card ((Finset.range (h₀ + 1)).image (fun i : ℕ => (↑i : ℤ))) := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
            obtain ⟨j, _, rfl⟩ := hx
            rw [hpos_j j]
            exact ⟨min j h₀, by omega, by push_cast; rfl⟩
        _ ≤ h₀ + 1 := by
            rw [Finset.card_image_of_injective _ (fun a b hab => by exact_mod_cast hab)]
            simp [Finset.card_range]
        _ ≤ w.length + 2 := by omega



/-- Number of bits needed to encode a configuration of a `spacebound`-space TM running
on input `w`: state + tape contents + head position. -/
def tqbfConfigSize {Q : Type} {Γ : Type} (_M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : ℕ :=
  spacebound + w.length + 1

/-- Number of recursion levels in the TQBF reduction: one level per bit of space. -/
def tqbfNumLevels (spacebound : ℕ) : ℕ := spacebound + 1

/-- A trivial conjunction `x_{n-1} ∧ x_{n-2} ∧ … ∧ x_0 ∧ True` used as a placeholder
body when building the TQBF formula. -/
def tqbfBaseBody : ℕ → NPCompleteness.BoolFormula
  | 0 => .trueConst
  | n + 1 => .and (.var n) (tqbfBaseBody n)

/-- The variables of `tqbfBaseBody n` are exactly `{0, 1, …, n-1}`. -/
lemma tqbfBaseBody_vars (n : ℕ) :
    (tqbfBaseBody n).vars = Finset.range n := by
  induction n with
  | zero => simp [tqbfBaseBody, NPCompleteness.BoolFormula.vars, Finset.range_zero]
  | succ k ih =>
    simp only [tqbfBaseBody, NPCompleteness.BoolFormula.vars, ih]
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
    omega

/-- Wraps `q` with `n` alternating quantifiers `∃ k. … ∀ k. …` according to the
divisibility pattern used in the halving construction for the PSPACE-completeness proof
of TQBF. -/
def quantifyHalving (q : QBF) (configSize : ℕ) : ℕ → QBF
  | 0 => q
  | k + 1 =>

    if (k + 1) % (configSize + 1) == 0 then
      QBF.forall_ k (quantifyHalving q configSize k)
    else
      QBF.exists_ k (quantifyHalving q configSize k)

/-- Quantifying `q` with `quantifyHalving … n` removes the variables `0, …, n-1` from
the free-variable set. -/
lemma freeVars_quantifyHalving (q : QBF) (configSize : ℕ) (n : ℕ) :
    (quantifyHalving q configSize n).freeVars = q.freeVars \ Finset.range n := by
  induction n with
  | zero => simp [quantifyHalving, Finset.range_zero]
  | succ k ih =>
    simp only [quantifyHalving]
    split
    ·
      simp only [QBF.freeVars, ih, Finset.erase_eq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_range]
      constructor
      · intro ⟨⟨hx1, hx2⟩, hne⟩; exact ⟨hx1, by omega⟩
      · intro ⟨hx1, hx2⟩; exact ⟨⟨hx1, by omega⟩, by omega⟩
    ·
      simp only [QBF.freeVars, ih, Finset.erase_eq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_range]
      constructor
      · intro ⟨⟨hx1, hx2⟩, hne⟩; exact ⟨hx1, by omega⟩
      · intro ⟨hx1, hx2⟩; exact ⟨⟨hx1, by omega⟩, by omega⟩

/-- Given a TM `M`, input `w`, and a space bound, construct a QBF whose truth is
equivalent to `M` accepting `w` in space `spacebound`. This is the Sipser construction
underlying the reduction `A ≤ₚ TQBF` for the PSPACE-hardness of TQBF. -/
noncomputable def buildTQBFFormula {Q : Type} [DecidableEq Q]
    {Γ : Type} (M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : QBF :=
  let configSize := tqbfConfigSize M w spacebound
  let numLevels := tqbfNumLevels spacebound
  let totalVars := numLevels * (configSize + 1)
  let baseBody := tqbfBaseBody totalVars
  let baseQBF := QBF.body baseBody
  quantifyHalving baseQBF configSize totalVars


/-- The constructed QBF `buildTQBFFormula M w spacebound` is a sentence: every variable
is quantified. -/
theorem buildTQBFFormula_isFullyQuantified {Q : Type} [DecidableEq Q]
    {Γ : Type} (M : TM Q Γ) (w : List Γ) (spacebound : ℕ) :
    (buildTQBFFormula M w spacebound).IsFullyQuantified := by
  unfold buildTQBFFormula QBF.IsFullyQuantified
  simp only []
  rw [freeVars_quantifyHalving]
  simp [QBF.freeVars, tqbfBaseBody_vars]



/-- The reduction function `w ↦ ⟨φ_{M,w}⟩` mapping inputs of a PSPACE machine `M` to
encoded QBFs. -/
noncomputable def tqbfReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (enc : QBFEncoding Γ) {Q : Type} [DecidableEq Q]
    (M : TM Q Γ) (g : ℕ → ℕ) : List Γ → List Γ := fun w =>
  enc.encode (buildTQBFFormula M w (g w.length))






end SpaceComplexity

namespace SpaceComplexity

/-- An encoding of Generalized Geography instances `(G, a)` (a digraph with a starting
node) as strings over alphabet `Γ`. -/
structure GGEncoding (Γ : Type) [Inhabited Γ] where
  V : Type
  decEqV : DecidableEq V
  encode : Digraph V × V → List Γ
  decode : List Γ → Option (Digraph V × V)
  encode_injective : Function.Injective encode
  decode_encode : ∀ p : Digraph V × V, decode (encode p) = some p
  blank_free : ∀ p : Digraph V × V, (default : Γ) ∉ encode p
  encode_decode : ∀ (l : List Γ) (p : Digraph V × V), decode l = some p → encode p = l
  fintypeV : Fintype V
  nonemptyV : Nonempty V

/-- The Generalized Geography language `GG = {⟨G, a⟩ | Player I has a forced win on G
starting at a}`, encoded over `Γ`. -/
def ggLanguage {Γ : Type} [Inhabited Γ] (enc : GGEncoding Γ) : Set (List Γ) :=
  {s | ∃ p : Digraph enc.V × enc.V,
    enc.encode p = s ∧ @GeographyGame.GG enc.V enc.decEqV p.1 p.2}


/-- State type for the GG-recognizing NTM: a control bit plus a buffer holding the input
read so far. -/
def GGState (Γ : Type) := Fin 3 × List Γ

/-- Decidable equality on `GGState Γ`, inherited from `Fin 3 × List Γ`. -/
instance ggStateDecEq (Γ : Type) [DecidableEq Γ] : DecidableEq (GGState Γ) :=
  inferInstanceAs (DecidableEq (Fin 3 × List Γ))

/-- The GG-recognizing NTM: scans the input, decodes it as a digraph `(G, a)`, and
accepts iff Player I has a forced win in Generalized Geography on `G` from `a`. -/
noncomputable def ggNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : GGEncoding Γ) : NTM (GGState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some p => @decide (@GeographyGame.GG enc.V enc.decEqV p.1 p.2)
              (Classical.dec _)
          | none => false
        if result then
          {((⟨1, by omega⟩, ([] : List Γ)), default, Direction.R)}
        else
          {((⟨2, by omega⟩, ([] : List Γ)), default, Direction.R)}
      else
        {((⟨0, by omega⟩, buf ++ [a]), a, Direction.R)}
    | (⟨1, _⟩, _) => ∅
    | (⟨2, _⟩, _) => ∅
    | _ => ∅
  q₀ := (⟨0, by omega⟩, [])
  qAccept := (⟨1, by omega⟩, [])
  qReject := (⟨2, by omega⟩, [])
  qReject_ne_qAccept := by simp [GGState]

set_option maxRecDepth 2048 in
/-- The NTM `ggNTM enc` recognizes exactly the encoded GG language. -/
theorem ggNTM_language {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : GGEncoding Γ) :
    (ggNTM enc).language = ggLanguage enc := by
  set M := ggNTM enc with M_def
  ext w
  simp only [NTM.language, Set.mem_setOf_eq, ggLanguage, Set.mem_setOf_eq]
  constructor
  ·
    intro ⟨hAlpha, branch, k, hValid, hAccept⟩
    have hNonBlank : ∀ s ∈ w, s ≠ (default : Γ) := fun s hs => hAlpha s hs
    have scanInv : ∀ i : ℕ, i ≤ w.length →
        (branch i).state = ((⟨0, by omega⟩ : Fin 3), w.take i) ∧
        (branch i).headPos = (i : ℤ) ∧
        (branch i).tape = (M.initConfig w).tape := by
      intro i hi
      induction i with
      | zero =>
        exact ⟨congr_arg Config.state hValid.1, congr_arg Config.headPos hValid.1,
               congr_arg Config.tape hValid.1⟩
      | succ n ih =>
        have hn : n < w.length := Nat.lt_of_succ_le hi
        obtain ⟨hS, hH, hT⟩ := ih (Nat.le_of_lt hn)
        have hNotHalt : ¬M.isHaltConfig (branch n) := by
          simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM]
          rw [hS]; intro h; rcases h with h | h <;> simp [GGState] at h
        have hStep := (hValid.2 n).1 hNotHalt
        have hRead : (branch n).tape (branch n).headPos = w.get ⟨n, hn⟩ := by
          rw [hT, hH]; simp [NTM.initConfig, M_def, ggNTM, show (0 : ℤ) ≤ (n : ℤ) from by omega,
            show (n : ℤ) < (w.length : ℤ) from by omega]
        have hSymNB : w.get ⟨n, hn⟩ ≠ (default : Γ) :=
          hNonBlank _ (List.get_mem w ⟨n, hn⟩)
        obtain ⟨_, q', b, d, hMem, hSt, hHd, hTp⟩ := hStep
        have hTrEq : (q', b, d) = ((⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]),
            w.get ⟨n, hn⟩, Direction.R) := by
          have h := hMem; rw [hS, hRead] at h
          simp only [M_def, ggNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff] at h
          exact h
        obtain ⟨hq', hb, hd⟩ : q' = (⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]) ∧
            b = w.get ⟨n, hn⟩ ∧ d = Direction.R :=
          ⟨congr_arg Prod.fst hTrEq, congr_arg (fun x => x.2.1) hTrEq,
           congr_arg (fun x => x.2.2) hTrEq⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hSt, hq', List.take_succ_eq_append_getElem hn]; simp [List.get_eq_getElem]
        · rw [hHd, hd, hH]; norm_cast
        · rw [hTp, hT, hH, hb, ← hRead, hT, hH]; exact Function.update_eq_self _ _
    obtain ⟨hS_end, hH_end, hT_end⟩ := scanInv w.length le_rfl
    rw [List.take_length] at hS_end
    have hNotHalt_end : ¬M.isHaltConfig (branch w.length) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM]
      rw [hS_end]; intro h; rcases h with h | h <;> simp [GGState] at h
    have hReadBlank : (branch w.length).tape (branch w.length).headPos = (default : Γ) := by
      rw [hT_end, hH_end]; simp [NTM.initConfig, M_def, ggNTM]
    have hStepEnd := (hValid.2 w.length).1 hNotHalt_end
    obtain ⟨_, q'', b'', d'', hMem'', hSt'', _, _⟩ := hStepEnd
    have hTransIn : (q'', b'', d'') ∈ M.δ ((⟨0, by omega⟩ : Fin 3), w) (default : Γ) := by
      have h := hMem''; rwa [hS_end, hReadBlank] at h
    have hNotAccBefore : ∀ i, i ≤ w.length → (branch i).state ≠ M.qAccept := by
      intro i hi hEq; have ⟨hSi, _, _⟩ := scanInv i hi
      rw [hSi] at hEq; simp [M_def, ggNTM, GGState] at hEq
    have hk_gt : k > w.length := by
      by_contra h; push_neg at h; exact hNotAccBefore k h hAccept
    have hHalt_next : M.isHaltConfig (branch (w.length + 1)) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM, hSt'']
      simp only [M_def, ggNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      split_ifs at hTransIn <;> (obtain ⟨rfl, -, -⟩ := hTransIn; simp [GGState])
    have hConst : ∀ j, j ≥ w.length + 1 → branch j = branch (w.length + 1) := by
      intro j hj; induction j with
      | zero => omega
      | succ m ihm =>
        by_cases hm : m ≥ w.length + 1
        · have heq := ihm hm
          exact ((hValid.2 m).2 (heq ▸ hHalt_next)).symm ▸ heq
        · push_neg at hm; congr 1; omega
    have hAccNext : (branch (w.length + 1)).state = M.qAccept := by
      have := hConst k (by omega); rw [← this]; exact hAccept
    have hq''_acc : q'' = ((⟨1, by omega⟩ : Fin 3), ([] : List Γ)) := by
      rw [hSt''] at hAccNext; exact hAccNext
    have hResultTrue : (match enc.decode w with
        | some p => @decide (@GeographyGame.GG enc.V enc.decEqV p.1 p.2) (Classical.dec _)
        | none => false) = true := by
      by_contra hFalse; push_neg at hFalse; simp only [Bool.not_eq_true] at hFalse
      simp only [M_def, ggNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      simp only [hFalse, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      obtain ⟨rfl, -, -⟩ := hTransIn
      simp [GGState] at hq''_acc
    cases hDec : enc.decode w with
    | none => simp [hDec] at hResultTrue
    | some p =>
      simp [hDec] at hResultTrue
      exact ⟨p, enc.encode_decode w p hDec, hResultTrue⟩
  ·
    intro ⟨p, hEncode, hGG⟩
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [M_def, ggNTM, NTM.inputAlpha, Set.mem_setOf_eq]
      exact fun heq => enc.blank_free p (hEncode ▸ heq ▸ hs)
    · refine ⟨fun n =>
        if n ≤ w.length then
          ⟨((⟨0, by omega⟩ : Fin 3), w.take n), (n : ℤ), (M.initConfig w).tape⟩
        else
          ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), ((w.length : ℤ) + 1),
           Function.update (M.initConfig w).tape (↑w.length) default⟩,
        w.length + 1, ?_, ?_⟩
      · constructor
        · simp [NTM.initConfig, M_def, ggNTM]
        · intro n; constructor
          · intro hNotHalt
            simp only [NTM.step]; refine ⟨hNotHalt, ?_⟩
            by_cases hn_le : n ≤ w.length
            · by_cases hn_lt : n < w.length
              · simp only [hn_le, ↓reduceIte]
                have hRead : (M.initConfig w).tape (↑n) = w.get ⟨n, hn_lt⟩ := by
                  simp [NTM.initConfig, M_def, ggNTM,
                    show (0 : ℤ) ≤ (n : ℤ) from by omega,
                    show (n : ℤ) < (w.length : ℤ) from by omega]
                have hSymNB : w.get ⟨n, hn_lt⟩ ≠ (default : Γ) := by
                  exact fun h => enc.blank_free p (hEncode ▸ h ▸ List.get_mem w ⟨n, hn_lt⟩)
                refine ⟨((⟨0, by omega⟩ : Fin 3), w.take n ++ [w.get ⟨n, hn_lt⟩]),
                         w.get ⟨n, hn_lt⟩, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, _⟩, w.take n)) ((M.initConfig w).tape ↑n)
                  rw [hRead]
                  simp only [M_def, ggNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff]
                  simp only [List.get_eq_getElem]
                  rfl
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [List.take_succ_eq_append_getElem hn_lt]; simp [List.get_eq_getElem]
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]; norm_cast
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [← hRead]; exact (Function.update_eq_self ((↑n : ℤ)) _).symm
              · have hn_eq : n = w.length := Nat.le_antisymm hn_le (by omega)
                subst hn_eq
                simp only [le_refl, ↓reduceIte, List.take_length]
                have hReadBl : (M.initConfig w).tape (↑w.length : ℤ) = (default : Γ) := by
                  simp [NTM.initConfig, M_def, ggNTM]
                have hDecW : enc.decode w = some p := by rw [← hEncode]; exact enc.decode_encode p
                have hResult : (match enc.decode w with
                    | some p' => @decide (@GeographyGame.GG enc.V enc.decEqV p'.1 p'.2) (Classical.dec _)
                    | none => false) = true := by
                  rw [hDecW]; simp only [decide_eq_true_eq]; exact hGG
                refine ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), default, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, (by omega : (0 : Fin 3).val < 3)⟩, w)) ((M.initConfig w).tape ↑w.length)
                  rw [hReadBl]
                  simp only [M_def, ggNTM, ↓reduceIte, hResult, Set.mem_singleton_iff]
                  rfl
                · simp [show ¬(w.length + 1 ≤ w.length) from by omega]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false, Direction]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false]
            · exfalso; apply hNotHalt
              simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM,
                show ¬(n ≤ w.length) from hn_le, ↓reduceIte]
              left; trivial
          · intro hHalt
            by_cases hn_le : n ≤ w.length
            · exfalso; apply hHalt.elim <;> intro h <;>
                simp [NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM, hn_le, GGState] at h
            · simp [show ¬(n ≤ w.length) from hn_le, show ¬(n + 1 ≤ w.length) from by omega]
      · simp only [NTM.isAcceptConfig, M_def, ggNTM, show ¬(w.length + 1 ≤ w.length) from by omega,
          ↓reduceIte]





/-- The Sipser TQBF→GG reduction: build a Generalized Geography instance whose Player-I
forced wins correspond exactly to truth of the QBF `ψ`. (Uses choice to witness the
existence of an appropriate digraph.) -/
noncomputable def buildFormulaGameGraph
    {Γ : Type} [Inhabited Γ] (genc : GGEncoding Γ) (ψ : QBF) :
    Digraph genc.V × genc.V :=
  haveI hne : Nonempty genc.V := genc.nonemptyV
  haveI : Nonempty (Digraph genc.V × genc.V) :=
    ⟨⟨⟨fun _ _ => False⟩, Classical.choice hne⟩⟩
  Classical.epsilon (fun p : Digraph genc.V × genc.V =>
    @GeographyGame.GG genc.V genc.decEqV p.1 p.2 ↔ (ψ.IsFullyQuantified ∧ ψ.IsTrue))



/-- The string-level reduction from encoded QBFs to encoded GG instances. -/
noncomputable def ggReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (qenc : QBFEncoding Γ) (genc : GGEncoding Γ) : List Γ → List Γ := fun w =>
  match qenc.decode w with
  | some ψ => genc.encode (buildFormulaGameGraph genc ψ)
  | none   => default










end SpaceComplexity
