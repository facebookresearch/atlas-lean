/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Countable
import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

import Atlas.TheoryOfComputation.code.TuringMachines
import Atlas.TheoryOfComputation.code.Reductions

namespace Decidability

/-- A set `s : Set α` is countable if it is finite or has the same size as `ℕ`. -/
def IsCountable {α : Type*} (s : Set α) : Prop := s.Countable

/-- For any countably infinite type `α`, the power set `Set α` is uncountable.
This is a form of Cantor's theorem and underlies the proof that some language is undecidable. -/
theorem set_not_countable_of_countable_infinite {α : Type*} [Countable α] [Infinite α] :
    ¬ Countable (Set α) := by
  intro h
  obtain ⟨f, hf⟩ := exists_injective_nat (Set α)
  haveI : Denumerable α := Denumerable.mk' (nonempty_equiv_of_countable.some)
  let e := (Denumerable.eqv α).symm
  exact Function.cantor_injective (e ∘ f) (e.injective.comp hf)

/-- **Corollary (Sipser Lecture 8).** The set ℒ of all languages over a nonempty countable
alphabet is uncountable. Combined with the countability of Turing machines, this shows that
some language is not Turing-decidable. -/
theorem languages_uncountable (Alphabet : Type*) [Nonempty Alphabet] [Countable Alphabet] :
    ¬ Countable (Language Alphabet) :=
  set_not_countable_of_countable_infinite

end Decidability

open TuringMachine

/-- A `TMDesc` packages a Turing machine together with its (decidable) state type and an input
string. This corresponds to the encoded pair `⟨M, w⟩` used throughout Sipser's undecidability
arguments — for example, the input to a putative decider for `A_TM`. -/
structure TuringMachine.TMDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  tm : TuringMachine.TM Q Γ
  input : List Γ

namespace TuringMachine

variable {Γ : Type}

/-- `d.accepts` holds when the underlying TM `d.tm` accepts the input `d.input`. -/
def TMDesc.accepts (d : TMDesc Γ) : Prop :=
  @TM.accepts d.Q Γ d.decEq d.tm d.input

/-- `d.halts` holds when the underlying TM `d.tm` halts (accepts or rejects) on the input
`d.input`. -/
def TMDesc.halts (d : TMDesc Γ) : Prop :=
  @TM.halts d.Q Γ d.decEq d.tm d.input

/-- Additivity of `run`: running `M` for `m + n` steps equals running it for `m` steps and
then for an additional `n` steps. -/
theorem TM.run_add {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c : Config Q Γ) (m n : ℕ) :
    M.run c (m + n) = M.run (M.run c m) n := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    show M.step (M.run c (m + n)) = M.step (M.run (M.run c m) n)
    rw [ih]

end TuringMachine

/-- A `TMEncoding` over alphabet `Γ` is a bundle of all the encoding/universal-machine
machinery used informally in Sipser. It provides:
* an injective encoding `encode : TMDesc Γ → List Γ` with a decoder,
* a self-reference principle (used for the Recursion Theorem / diagonal argument),
* a universal TM `U` that simulates encoded TMs whenever they halt,
* sequential composition of a decider with another TM, and
* transducer composition with computable functions, as used in mapping reductions. -/
structure TuringMachine.TMEncoding (Γ : Type) where
  encode : TuringMachine.TMDesc Γ → List Γ
  decode : List Γ → Option (TuringMachine.TMDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d
  selfRef : ∀ {Q₀ : Type} [DecidableEq Q₀] (M : TuringMachine.TM Q₀ Γ),
    ∃ d : TuringMachine.TMDesc Γ,
      d.accepts ↔ @TuringMachine.TM.accepts Q₀ Γ _ M (encode d)
  universalSim : ∃ (QU : Type) (_ : DecidableEq QU) (U : TuringMachine.TM QU Γ),
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      @TuringMachine.TM.halts QU Γ _ U (encode d)) ∧
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      (@TuringMachine.TM.accepts QU Γ _ U (encode d) ↔ d.accepts)) ∧
    (∀ s, @TuringMachine.TM.accepts QU Γ _ U s →
      ∃ d : TuringMachine.TMDesc Γ, encode d = s ∧ d.accepts)
  sequentialComposition : ∀ {QR QU : Type}
    [DecidableEq QR] [DecidableEq QU]
    (R : TuringMachine.TM QR Γ) (U : TuringMachine.TM QU Γ),
    R.isDecider →
    (∀ w, @TuringMachine.TM.accepts QR Γ _ R w →
      @TuringMachine.TM.halts QU Γ _ U w) →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        (@TuringMachine.TM.accepts QR Γ _ R w ∧
         @TuringMachine.TM.accepts QU Γ _ U w))
  transducerComposition : ∀ (f : List Γ → List Γ),
    TuringMachine.IsComputableFunction f →
    ∀ {QR : Type} [DecidableEq QR] (R : TuringMachine.TM QR Γ),
    R.isDecider →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        @TuringMachine.TM.accepts QR Γ _ R (f w))

namespace TuringMachine



end TuringMachine

namespace TuringMachine

variable {Γ : Type}

/-- The acceptance problem for Turing machines: `A_TM = {⟨M, w⟩ | M accepts w}`.
The classical Sipser theorem says this language is undecidable but Turing-recognizable. -/
def A_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.accepts}

/-- The halting problem: `HALT_TM = {⟨M, w⟩ | M halts on w}`, also undecidable. -/
def HALT_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.halts}

/-- If a TM accepts an input then it halts on that input (accepting is a form of halting). -/
theorem TM.halts_of_accepts {Q : Type} [DecidableEq Q] (M : TM Q Γ) (w : List Γ)
    (h : M.accepts w) : M.halts w := by
  obtain ⟨n, hacc⟩ := h
  exact ⟨n, Or.inl hacc⟩

/-- Acceptance implies halting at the level of languages: `A_TM ⊆ HALT_TM`. -/
theorem A_TM_subset_HALT_TM (enc : TMEncoding Γ) :
    A_TM enc ⊆ HALT_TM enc := by
  intro s ⟨d, henc, hacc⟩
  refine ⟨d, henc, ?_⟩
  obtain ⟨n, hacc'⟩ := hacc
  exact ⟨n, Or.inl hacc'⟩

end TuringMachine

/-- The "flipped" TM `H.flip` swaps the accept and reject states of `H`. If `H` is a decider
then `H.flip` decides the complement of `L(H)`. This is the standard construction used in the
diagonal proof that `A_TM` is undecidable. -/
def TuringMachine.TM.flip {Q : Type} (Γ : Type) [DecidableEq Q] (H : TuringMachine.TM Q Γ) :
    TuringMachine.TM Q Γ where
  blank := H.blank
  inputAlpha := H.inputAlpha
  blank_not_in_inputAlpha := H.blank_not_in_inputAlpha
  δ := H.δ
  q₀ := H.q₀
  qAccept := H.qReject
  qReject := H.qAccept
  qReject_ne_qAccept := H.qReject_ne_qAccept.symm

/-- Swapping accept/reject states does not change the one-step transition function of the TM
on non-halting configurations, and on halting configurations both sides idle, so the `step`
functions agree pointwise. -/
theorem TuringMachine.TM.flip_step {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ) :
    (H.flip Γ).step c = H.step c := by
  simp only [TuringMachine.TM.step, TuringMachine.TM.flip]
  split_ifs with h1 h2 h2
  · rfl
  ·
    exfalso; exact h2 (h1.elim Or.inr Or.inl)
  ·
    exfalso; exact h1 (h2.elim Or.inr Or.inl)
  · rfl

/-- The `n`-step run is the same for `H` and `H.flip`, since their step functions agree
pointwise. -/
theorem TuringMachine.TM.flip_run {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ) (n : ℕ) :
    (H.flip Γ).run c n = H.run c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [TuringMachine.TM.run, ih, H.flip_step]

/-- If `H` is a decider then its flip `H.flip` accepts `w` iff `H` does not accept `w`. This is
the crucial property that allows the flip to decide the complement language. -/
theorem TuringMachine.TM.flip_accepts_iff {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (hH : H.isDecider) (w : List Γ) :
    (H.flip Γ).accepts w ↔ ¬ H.accepts w := by

  have hrun_add : ∀ (c : TuringMachine.Config Q Γ) (a b : ℕ),
      H.run (H.run c a) b = H.run c (a + b) := by
    intro c a b; induction b with
    | zero => rfl
    | succ b ih =>
      change H.step (H.run (H.run c a) b) = _; rw [ih]; rfl

  have hrun_eq : ∀ n, (H.flip Γ).runOnInput w n = H.runOnInput w n := by
    intro n
    show (H.flip Γ).run ((H.flip Γ).initConfig w) n = H.run (H.initConfig w) n
    have hinit : (H.flip Γ).initConfig w = H.initConfig w := by
      simp [TuringMachine.TM.initConfig, TuringMachine.TM.flip]
    rw [hinit, H.flip_run]


  have h_eq : (H.flip Γ).accepts w ↔ H.rejects w := by
    constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
    · change (H.runOnInput w n).state = H.qReject
      change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept at hn
      rwa [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
           show (H.flip Γ).qAccept = H.qReject from rfl] at hn
    · change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept
      rw [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
          show (H.flip Γ).qAccept = H.qReject from rfl]
      exact hn
  rw [h_eq]
  constructor
  · rintro ⟨n, href⟩ ⟨m, hacc⟩

    have reject_persists : ∀ k,
        (H.run (H.run (H.initConfig w) n) k).state = H.qReject := by
      intro k
      induction k with
      | zero => exact href
      | succ k ihk =>
        show (H.step (H.run (H.run (H.initConfig w) n) k)).state = H.qReject
        rw [H.step_of_halt _ (Or.inr ihk)]; exact ihk
    have hstable2 := H.accepts_stable (H.runOnInput w m) n hacc
    simp only [TuringMachine.TM.runOnInput] at hstable2
    rw [hrun_add, show m + n = n + m from Nat.add_comm m n] at hstable2
    have hrej := reject_persists m
    rw [hrun_add] at hrej
    exact H.qReject_ne_qAccept (hrej.symm.trans hstable2)
  · intro hna
    obtain ⟨n, hn⟩ := hH w
    rcases hn with hacc | href
    · exact absurd ⟨n, hacc⟩ hna
    · exact ⟨n, href⟩

/-- **Theorem (Sipser, undecidability of A_TM).** The acceptance problem
`A_TM = {⟨M, w⟩ | M accepts w}` is not Turing-decidable. The proof is the classical Turing
diagonal argument: assuming a decider `H` exists, the flipped machine `D = H.flip` (which
decides whether `H` rejects) leads to a contradiction via the self-reference principle
provided by `TMEncoding`. -/
theorem TuringMachine.A_TM_not_decidable
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ) :
    ¬TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by
  intro ⟨QH, decEqH, H, hDecider, hLang⟩

  have hH_iff : ∀ d : TuringMachine.TMDesc Γ,
      @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d) ↔ d.accepts := by
    intro d
    have hLang' : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH H w ↔
        w ∈ TuringMachine.A_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QH Γ decEqH H ↔ w ∈ TuringMachine.A_TM enc
      rw [hLang]
    rw [hLang' (enc.encode d)]
    constructor
    · rintro ⟨d', henc, hacc⟩
      have := enc.encode_injective henc
      subst this
      exact hacc
    · intro hacc
      exact ⟨d, rfl, hacc⟩

  let D := @TuringMachine.TM.flip QH Γ decEqH H
  have hD : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH D w ↔
      ¬ @TuringMachine.TM.accepts QH Γ decEqH H w :=
    TuringMachine.TM.flip_accepts_iff H hDecider

  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef D

  have hcontra : d₀.accepts ↔ ¬ d₀.accepts := by
    calc d₀.accepts
        ↔ @TuringMachine.TM.accepts QH Γ decEqH D (enc.encode d₀) := hSelfRef
      _ ↔ ¬ @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d₀) := hD _
      _ ↔ ¬ d₀.accepts := not_congr (hH_iff d₀)

  by_cases h : d₀.accepts
  · exact hcontra.mp h h
  · exact h (hcontra.mpr h)

/-- A decider for `HALT_TM` yields a decider for `A_TM`. This is the standard reduction
`A_TM ≤ HALT_TM`: first use the `HALT_TM`-decider to check that `M` halts on `w`, then run the
universal TM `U` (which is guaranteed to halt on inputs whose underlying TM halts) to determine
whether `M` accepts. Together with the undecidability of `A_TM` this implies the undecidability
of `HALT_TM`. -/
theorem TuringMachine.A_TM_decidable_of_HALT_TM_decidable
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ)
    (hHalt : TuringMachine.IsTuringDecidable (TuringMachine.HALT_TM enc)) :
    TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by

  obtain ⟨QR, decEqR, R, hR_dec, hR_lang⟩ := hHalt

  obtain ⟨QU, decEqU, U, hU_halts, hU_accepts, _⟩ := enc.universalSim

  have hR_iff : ∀ d : TuringMachine.TMDesc Γ,
      @TuringMachine.TM.accepts QR Γ decEqR R (enc.encode d) ↔ d.halts := by
    intro d
    have : ∀ w, @TuringMachine.TM.accepts QR Γ decEqR R w ↔
        w ∈ TuringMachine.HALT_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QR Γ decEqR R ↔ w ∈ TuringMachine.HALT_TM enc
      rw [hR_lang]
    rw [this]
    exact ⟨fun ⟨d', henc, hhalts⟩ => enc.encode_injective henc ▸ hhalts,
           fun hhalts => ⟨d, rfl, hhalts⟩⟩

  have hU_halts_when_R_accepts : ∀ w,
      @TuringMachine.TM.accepts QR Γ decEqR R w →
      @TuringMachine.TM.halts QU Γ decEqU U w := by
    intro w hRw

    have hw_in_halt : w ∈ TuringMachine.HALT_TM enc := by
      have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
      rwa [hR_lang] at this
    obtain ⟨d, henc, hd_halts⟩ := hw_in_halt
    rw [← henc]
    exact hU_halts d hd_halts

  obtain ⟨QS, decEqS, S, hS_dec, hS_accepts⟩ :=
    enc.sequentialComposition R U hR_dec hU_halts_when_R_accepts

  exact ⟨QS, decEqS, S, hS_dec, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hS_accepts w]
    constructor
    ·
      rintro ⟨hRw, hUw⟩

      have hw_halt : w ∈ TuringMachine.HALT_TM enc := by
        have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
        rwa [hR_lang] at this
      obtain ⟨d, henc, hd_halts⟩ := hw_halt
      rw [TuringMachine.A_TM]
      exact ⟨d, henc, (hU_accepts d hd_halts).mp (henc ▸ hUw)⟩
    ·
      rintro ⟨d, henc, hd_acc⟩
      constructor
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hR_iff d).mpr hd_halts
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hU_accepts d hd_halts).mpr hd_acc⟩

namespace TuringMachine

/-- **Theorem (Sipser).** The halting problem `HALT_TM = {⟨M, w⟩ | M halts on w}` is
undecidable, by reduction from `A_TM`. -/
theorem HALT_TM_not_decidable
    {Γ : Type} (enc : TMEncoding Γ) : ¬IsTuringDecidable (HALT_TM enc) := by
  intro hHalt
  exact A_TM_not_decidable enc (A_TM_decidable_of_HALT_TM_decidable enc hHalt)

end TuringMachine

namespace Decidability

open TuringMachine

/-- The head movement directions `L` and `R` form a two-element `Fintype`. -/
instance : Fintype Direction where
  elems := {Direction.L, Direction.R}
  complete := fun x => by cases x <;> simp

/-- A language is "finitely Turing-decidable" if it is decided by some TM whose state set is
`Fin n` for some `n`. Up to renaming of states this is no weaker than `IsTuringDecidable`, but
restricting to `Fin n` makes the collection of such machines countable. -/
def IsTuringDecidableFinite {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (n : ℕ) (M : TM (Fin n) Γ), M.isDecider ∧ M.language = A

/-- The raw data of a finite-state Turing machine over `Γ`: a state count `n`, a blank symbol,
a transition function, and start/accept/reject states. This is the carrier used to enumerate
TMs in a countable family. -/
abbrev TMDescType (Γ : Type) :=
  Σ n : ℕ, Γ × (Fin n → Γ → Fin n × Γ × Direction) × Fin n × Fin n × Fin n

/-- For finite alphabets, the set of finite-state TM descriptions is countable. -/
instance tmDescType_countable (Γ : Type) [Fintype Γ] [DecidableEq Γ] :
    Countable (TMDescType Γ) :=
  inferInstance

/-- Map a piece of raw TM data to its language. If `qAccept = qReject` (ill-formed data) the
language is empty; otherwise it is the language of the corresponding `TM`. -/
noncomputable def tmDescToLang (Γ : Type) [DecidableEq Γ] :
    TMDescType Γ → Set (List Γ) :=
  fun ⟨n, blank, δ, q₀, qAccept, qReject⟩ =>
    if h : qReject ≠ qAccept then
      (TM.mk blank ∅ (Set.notMem_empty _) δ q₀ qAccept qReject h : TM (Fin n) Γ).language
    else ∅

/-- Two TMs that agree on blank, transition function, start, accept, and reject states
accept the same language. The "extra" data in a TM record (e.g. `inputAlpha`) does not affect
the language. -/
theorem TM.language_eq_of_same_data {Q Γ : Type} [DecidableEq Q]
    (M₁ M₂ : TM Q Γ)
    (hblank : M₁.blank = M₂.blank) (hδ : M₁.δ = M₂.δ)
    (hq₀ : M₁.q₀ = M₂.q₀) (hqA : M₁.qAccept = M₂.qAccept)
    (hqR : M₁.qReject = M₂.qReject) :
    M₁.language = M₂.language := by
  have hstep : ∀ c, M₁.step c = M₂.step c := fun c => by
    simp only [TM.step, hδ, hqA, hqR]
  have hrun : ∀ c k, M₁.run c k = M₂.run c k := by
    intro c k; induction k with
    | zero => rfl
    | succ k ih => simp only [TM.run, ih, hstep]
  ext w
  simp only [TM.language, Set.mem_setOf_eq, TM.accepts, TM.isAcceptConfig,
    TM.runOnInput, hqA, hblank, hq₀, TM.initConfig, hrun]

/-- Every language of a TM with state set `Fin n` arises as `tmDescToLang` of some encoded
description. -/
theorem language_in_range_tmDescToLang {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    {n : ℕ} (M : TM (Fin n) Γ) :
    M.language ∈ Set.range (tmDescToLang Γ) := by
  refine ⟨⟨n, M.blank, M.δ, M.q₀, M.qAccept, M.qReject⟩, ?_⟩
  simp only [tmDescToLang, dif_pos M.qReject_ne_qAccept]
  exact TM.language_eq_of_same_data _ _ rfl rfl rfl rfl rfl

/-- **Corollary (Sipser Lecture 8).** Some language is not Turing-decidable. The argument is
the cardinality argument: there are only countably many Turing machines but uncountably many
languages, so some language cannot be decided. -/
theorem exists_undecidable_language (Γ : Type) [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] :
    ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L := by
  by_contra hall
  push Not at hall


  have hsurj : Function.Surjective (tmDescToLang Γ) := by
    intro L
    obtain ⟨n, M, _, hL⟩ := hall L
    obtain ⟨enc, henc⟩ := language_in_range_tmDescToLang M
    exact ⟨enc, by rw [henc, hL]⟩

  have hcount : Countable (Set (List Γ)) := hsurj.countable

  exact set_not_countable_of_countable_infinite hcount

/-- An explicit witness to "some language is undecidable": `A_TM` itself is undecidable. -/
theorem exists_undecidable_language' {Γ : Type} (enc : TMEncoding Γ) :
    ∃ A : Set (List Γ), ¬ IsTuringDecidable A :=
  ⟨A_TM enc, A_TM_not_decidable enc⟩

/-- Restatement: there exists a language over `Γ` that is not Turing-decidable. -/
theorem some_language_not_decidable (Γ : Type) [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] :
    ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L :=
  exists_undecidable_language Γ

end Decidability

namespace PostCorrespondence

/-- A *domino* in the Post Correspondence Problem is a pair of strings (`top`, `bottom`) over
the alphabet `α`. -/
structure Domino (α : Type) where
  top : List α
  bottom : List α

/-- A *PCP instance* is a finite list of dominoes. -/
def PCPInstance (α : Type) := List (Domino α)

/-- A PCP instance `P` *has a match* if there is a nonempty sequence of indices `i₁, …, iₖ` such
that concatenating the tops in order produces the same string as concatenating the bottoms in
order. The PCP language is precisely the set of encoded instances with a match. -/
def hasMatch {α : Type} (P : PCPInstance α) : Prop :=
  ∃ (indices : List (Fin P.length)),
    indices ≠ [] ∧
    (indices.map (fun i => (P.get i).top)).flatten =
    (indices.map (fun i => (P.get i).bottom)).flatten

/-- An injective encoding/decoding scheme that turns PCP instances over `Γ` into strings
over `Γ`. -/
structure PCPEncoding (Γ : Type) where
  encode : PCPInstance Γ → List Γ
  decode : List Γ → Option (PCPInstance Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ P, decode (encode P) = some P

variable {Γ : Type}

/-- The Post Correspondence Problem language `PCP = {⟨P⟩ | P has a match}`. By Sipser's
Lecture 10 theorem, this language is undecidable. -/
def PCP (enc : PCPEncoding Γ) : Set (List Γ) :=
  {s | ∃ P : PCPInstance Γ, enc.encode P = s ∧ hasMatch P}

end PostCorrespondence

namespace LBADecidability

open TuringMachine

/-- An `LBADesc` packages a linearly bounded automaton (a finite-state TM constrained to its
input region) with an input string. Following Sipser, `LBA = ⟨B, w⟩` is the typical input to
`A_LBA`. -/
structure LBADesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq
  input : List Γ

variable {Γ : Type}

/-- `d.accepts` holds when the LBA `d.lba` accepts the input string `d.input`. -/
def LBADesc.accepts (d : LBADesc Γ) : Prop :=
  @LBA.accepts d.Q Γ d.decEq d.lba d.input

/-- Injective encoding/decoding of `LBADesc`s into strings, used to formulate the language
`A_LBA`. -/
structure LBAEncoding (Γ : Type) where
  encode : LBADesc Γ → List Γ
  decode : List Γ → Option (LBADesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The acceptance language for LBAs: `A_LBA = {⟨B, w⟩ | LBA B accepts w}`. Sipser's Lecture 10
theorem shows this language is *decidable*. -/
def A_LBA (enc : LBAEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBADesc Γ, enc.encode d = s ∧ d.accepts}

/-- A *bounded configuration* records only the data of an LBA configuration that can vary in
the bounded simulation: state, head position in `Fin m`, and tape contents on the first `m`
cells. The total number of such configurations is finite. -/
def BoundedConfig (Q : Type) (Γ : Type) (m : ℕ) :=
  Q × Fin m × (Fin m → Γ)

/-- The set of bounded configurations of an LBA with state set `Q`, tape alphabet `Γ`, and
input bound `m` is finite when `Q` and `Γ` are. This finiteness is the basis of the decidability
of `A_LBA`: an LBA either accepts within `|Q| · m · |Γ|^m` steps or loops. -/
noncomputable instance instFintypeBoundedConfig (Q : Type) (Γ : Type) (m : ℕ)
    [Fintype Q] [DecidableEq Γ] [Fintype Γ] : Fintype (BoundedConfig Q Γ m) := by
  change Fintype (Q × Fin m × (Fin m → Γ))
  infer_instance

/-- Extract the bounded-configuration view of a TM configuration whose head lies in `[0, m)`. -/
def extractBoundedConfig {Q Γ : Type} (m : ℕ) (c : Config Q Γ)
    (h0 : 0 ≤ c.headPos) (h1 : c.headPos < ↑m) : BoundedConfig Q Γ m :=
  (c.state,
   ⟨c.headPos.toNat, by omega⟩,
   fun i => c.tape ↑i)

/-- An LBA never modifies tape cells outside the input region `[0, max 1 |w|)`: for any
position `i` outside this region, the tape symbol after `n` steps equals the initial symbol. -/
theorem lba_tape_outside_unchanged {Q Γ : Type} [DecidableEq Q]
    (B : LBA Q Γ) (w : List Γ) (n : ℕ) (i : ℤ)
    (hi : i < 0 ∨ ↑(max 1 w.length) ≤ i) :
    (B.toTM.runOnInput w n).tape i = (B.toTM.initConfig w).tape i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.runOnInput, TM.run] at *
    rw [TM.step]
    split_ifs with hhalt
    · exact ih
    · simp only
      have hbnd := B.head_bounded w n
      simp only [TM.runOnInput] at hbnd
      have hne : i ≠ (B.toTM.run (B.toTM.initConfig w) n).headPos := by
        rcases hi with hi | hi <;> omega
      simp only [Function.update, dif_neg hne]
      exact ih

/-- If two configurations of an LBA running on input `w` agree on their bounded views (state,
head position, and tape contents in `[0, max 1 |w|)`) then they are equal as full
configurations, since the tape outside that window is fixed. This is the key lemma underlying
the pigeonhole argument that bounds LBA running time. -/
theorem lba_configs_eq_of_bounded_eq {Q Γ : Type} [DecidableEq Q]
    (B : LBA Q Γ) (w : List Γ) (n₁ n₂ : ℕ)
    (h : extractBoundedConfig (max 1 w.length)
           (B.toTM.runOnInput w n₁)
           (B.head_bounded w n₁).1
           (B.head_bounded w n₁).2 =
         extractBoundedConfig (max 1 w.length)
           (B.toTM.runOnInput w n₂)
           (B.head_bounded w n₂).1
           (B.head_bounded w n₂).2) :
    B.toTM.runOnInput w n₁ = B.toTM.runOnInput w n₂ := by
  simp only [extractBoundedConfig, BoundedConfig, Prod.mk.injEq] at h
  obtain ⟨hstate, hhead_fin, htape⟩ := h
  have hhead : (B.toTM.runOnInput w n₁).headPos =
      (B.toTM.runOnInput w n₂).headPos := by
    simp only [Fin.mk.injEq] at hhead_fin
    have h1 := (B.head_bounded w n₁).1
    have h2 := (B.head_bounded w n₂).1
    omega
  have htape_eq : (B.toTM.runOnInput w n₁).tape =
      (B.toTM.runOnInput w n₂).tape := by
    funext i
    by_cases hrange : 0 ≤ i ∧ i < ↑(max 1 w.length)
    · have := congr_fun htape ⟨i.toNat, by omega⟩
      simp only at this
      convert this using 1 <;> simp [Int.toNat_of_nonneg hrange.1]
    · push Not at hrange

      have hi : i < 0 ∨ ↑(max 1 w.length) ≤ i := by
        by_cases h0 : 0 ≤ i
        · exact Or.inr (hrange h0)
        · exact Or.inl (by omega)
      rw [lba_tape_outside_unchanged B w n₁ i hi,
          lba_tape_outside_unchanged B w n₂ i hi]
  exact Config.mk.injEq _ _ _ _ _ _ |>.mpr ⟨hstate, hhead, htape_eq⟩

/-- Acceptance of an LBA description is decidable (classically). Constructively this follows
from the finiteness of LBA configurations, which bounds the search for an accepting run. -/
noncomputable instance lbaDesc_accepts_decidable
    (d : LBADesc Γ) : Decidable d.accepts := Classical.dec _




end LBADecidability

namespace ELBA

open TuringMachine

/-- An `LBAMachineDesc` is an LBA on its own (no input attached), used for the emptiness
problem `E_LBA`. -/
structure LBAMachineDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq

variable {Γ : Type}

/-- The language accepted by an LBA description. -/
def LBAMachineDesc.language (d : LBAMachineDesc Γ) : Set (List Γ) :=
  @LBA.language d.Q Γ d.decEq d.lba

/-- Injective encoding/decoding of LBA machine descriptions, used to formulate `E_LBA`. -/
structure LBAMachineEncoding (Γ : Type) where
  encode : LBAMachineDesc Γ → List Γ
  decode : List Γ → Option (LBAMachineDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The emptiness problem for LBAs: `E_LBA = {⟨B⟩ | L(B) = ∅}`. By Sipser's Lecture 10 theorem,
this language is undecidable. -/
def E_LBA (enc : LBAMachineEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBAMachineDesc Γ, enc.encode d = s ∧ d.language = ∅}

end ELBA











namespace ELBA

open TuringMachine


end ELBA

open TuringMachine in
/-- **Theorem.** `A_TM` is Turing-recognizable: the universal TM `U` provided by the encoding
serves as a recognizer. On input `⟨M, w⟩`, `U` simulates `M` on `w` and accepts iff `M` does. -/
theorem A_TM_recognizable
    {Γ : Type} (enc : TMEncoding Γ) :
    IsTuringRecognizable (A_TM enc) := by
  obtain ⟨QU, hQU, U, _hU_halts, hU_accepts, hU_valid⟩ := enc.universalSim
  refine ⟨QU, hQU, U, ?_⟩
  ext s
  simp only [TM.language, Set.mem_setOf_eq, A_TM]
  constructor
  ·
    exact hU_valid s
  ·
    rintro ⟨d, rfl, hd_acc⟩
    have hd_halts : d.halts := @TM.halts_of_accepts Γ d.Q d.decEq d.tm d.input hd_acc
    exact (hU_accepts d hd_halts).mpr hd_acc

namespace TuringMachine


end TuringMachine


namespace AllCFG

open TuringMachine

/-- An injective encoding/decoding scheme that turns context-free grammars over `Γ` into
strings over `Γ`. Used to formulate `ALL_CFG`. -/
structure CFGEncoding (Γ : Type) where
  encode : ContextFreeGrammar Γ → List Γ
  decode : List Γ → Option (ContextFreeGrammar Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ g, decode (encode g) = some g



variable {Γ : Type}

/-- The universality problem for CFGs: `ALL_CFG = {⟨G⟩ | G is a CFG and L(G) = Σ*}`. By
Sipser's Lecture 10 theorem, this language is undecidable. -/
def ALL_CFG (enc : CFGEncoding Γ) : Set (List Γ) :=
  {s | ∃ g : ContextFreeGrammar Γ, enc.encode g = s ∧ g.language = Set.univ}

end AllCFG





namespace AllCFG

open TuringMachine


end AllCFG


/-- **Sipser Lecture 9 (mapping reductions preserve decidability).** If `A ≤ₘ B` and `B` is
decidable, then so is `A`: compose the reduction transducer with the decider for `B`. -/
theorem TuringMachine.isTuringDecidable_of_mappingReducible
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ)
    {A B : Set (List Γ)}
    (hAB : TuringMachine.MappingReducible A B)
    (hB : TuringMachine.IsTuringDecidable B) :
    TuringMachine.IsTuringDecidable A := by
  obtain ⟨f, hf_comp, hf_red⟩ := hAB
  obtain ⟨Q_B, decEq_B, M_B, hDec_B, hLang_B⟩ := hB
  obtain ⟨Q_S, decEq_S, S, hDec_S, hAcc_S⟩ := enc.transducerComposition f hf_comp M_B hDec_B
  exact ⟨Q_S, decEq_S, S, hDec_S, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hAcc_S w]
    constructor
    · intro hacc
      have : f w ∈ @TuringMachine.TM.language Q_B Γ decEq_B M_B := hacc
      rw [hLang_B] at this
      exact (hf_red w).mpr this
    · intro hw
      have : f w ∈ B := (hf_red w).mp hw
      rw [← hLang_B] at this
      exact this⟩






namespace PostCorrespondence


end PostCorrespondence
