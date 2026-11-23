/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.Reductions
import Atlas.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set

namespace SelfReference

open TuringMachine

/-- A self-contained description of a Turing machine over the tape alphabet `Γ`.
Bundles the (existential) state type `Q`, its `DecidableEq` instance, the underlying
`TM`, and an optional explicit source/encoding `source : List Γ` used by certain
concrete encodings. -/
structure TMDescription (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  machine : TM Q Γ
  source : List Γ := []

/-- The language `L(d)` recognized by the Turing machine packaged inside `d`. -/
def TMDescription.lang {Γ : Type} (d : TMDescription Γ) : Set (List Γ) :=
  @TM.language d.Q Γ d.decEq d.machine

variable {Γ : Type}

/-- `M.haltsWithOutput w out` says that running `M.machine` on input `w` reaches a
halt configuration after some number of steps `n`, and at that point the first
`out.length` cells of the tape spell out `out`. This is the "halt with `out` on the
tape" predicate used to formalize the printing/output behavior of TMs. -/
def TMDescription.haltsWithOutput (M : TMDescription Γ) (w out : List Γ) : Prop :=
  letI := M.decEq
  ∃ n : ℕ,
    M.machine.isHaltConfig (M.machine.runOnInput w n) ∧
    Config.readTape (M.machine.runOnInput w n) out.length = out

/-- A `TMEncoding` packages the data Sipser uses to set up the self-reproducing
TM construction:
* `encode`  : turns a TM description into its string code `⟨M⟩`;
* `printTMDesc w` : the "printer" machine `P_w` that on any input halts with `w` on
  the tape (`printTMDesc_spec`);
* `q_computable` : the function `q(w) = ⟨P_w⟩` is computable.
This is the formal counterpart of the textbook Lemma giving the computable
function `q : Σ* → Σ*` with `q(w) = ⟨P_w⟩`. -/
structure TMEncoding (Γ : Type) where
  encode : TMDescription Γ → List Γ
  printTMDesc : List Γ → TMDescription Γ
  printTMDesc_spec : ∀ (w input : List Γ), (printTMDesc w).haltsWithOutput input w
  q_computable : TuringMachine.IsComputableFunction (fun w => encode (printTMDesc w))

/-- `IsMinimalTM enc d` says `d` is a *minimal* Turing machine for its language under
the encoding `enc`: no strictly shorter description `d'` recognizes the same
language. Formally, for every `d'`, `|⟨d'⟩| < |⟨d⟩|` implies `L(d') ≠ L(d)`. -/
def IsMinimalTM {Γ : Type} (enc : TMEncoding Γ) (d : TMDescription Γ) : Prop :=
  ∀ d' : TMDescription Γ,
    (enc.encode d').length < (enc.encode d).length → d'.lang ≠ d.lang

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}`: the set of codes of minimal Turing
machines under the encoding `enc`. This is the language whose
Turing-unrecognizability is shown via the Recursion Theorem. -/
def MIN_TM {Γ : Type} (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDescription Γ, enc.encode d = s ∧ IsMinimalTM enc d}

/-- The data needed to build Sipser's self-reproducing TM SELF.
Bundles:
* an encoding `encode : TMDescription → List Γ`;
* the printer-machine constructor `printTM` together with its halting spec;
* a sequential `compose` operator that runs `A` then `B` (output of `A` becomes
  input of `B`) and whose code is some concatenation `combineDesc (encode A)
  (encode B)`;
* a "quine helper" `quineB` that on input `input` halts with
  `⟨P_input⟩ ⟨quineB⟩` on the tape.
This is exactly the structure used in the proof that some TM `SELF` prints its
own description on every input. -/
structure SelfRefFramework (Γ : Type) where
  encode : TMDescription Γ → List Γ
  printTM : List Γ → TMDescription Γ
  printTM_spec : ∀ (w input : List Γ), (printTM w).haltsWithOutput input w
  compose : TMDescription Γ → TMDescription Γ → TMDescription Γ
  compose_spec : ∀ (A B : TMDescription Γ) (w mid out : List Γ),
    A.haltsWithOutput w mid → B.haltsWithOutput mid out →
    (compose A B).haltsWithOutput w out
  combineDesc : List Γ → List Γ → List Γ
  encode_compose : ∀ (A B : TMDescription Γ),
    encode (compose A B) = combineDesc (encode A) (encode B)
  quineB : TMDescription Γ
  quineB_spec : ∀ (input : List Γ),
    quineB.haltsWithOutput input
      (combineDesc (encode (printTM input)) (encode quineB))

/-- The computable map `q(w) := ⟨P_w⟩` inside a `SelfRefFramework`: it sends a
string `w` to the code of the printer-machine that outputs `w`. -/
def SelfRefFramework.q (F : SelfRefFramework Γ) (w : List Γ) : List Γ :=
  F.encode (F.printTM w)

/-- An extension of `SelfRefFramework` exposing a concrete second-stage machine
`machineB` whose halting spec is stated directly in terms of the framework's
function `q`, matching the textbook construction `B(input) = ⟨P_q(input)⟩
⟨machineB⟩`. -/
structure SelfRefFrameworkExt (Γ : Type) extends SelfRefFramework Γ where
  machineB : TMDescription Γ
  machineB_spec : ∀ (input : List Γ),
    machineB.haltsWithOutput input
      (combineDesc (toSelfRefFramework.q input) (toSelfRefFramework.encode machineB))

/-- **Self-Reproducing TM** (Sipser, Lecture 11). Given a `SelfRefFramework F`,
there exists a TM `SELF` such that on every input `w`, `SELF` halts with `⟨SELF⟩`
on the tape. The witness is `SELF := compose (printTM ⟨quineB⟩) quineB`. -/
theorem exists_self_reproducing_tm (F : SelfRefFramework Γ) :
    ∃ (M : TMDescription Γ), ∀ (w : List Γ), M.haltsWithOutput w (F.encode M) := by

  let B := F.quineB
  have hB_spec := F.quineB_spec

  let descB := F.encode B
  let A := F.printTM descB

  let SELF := F.compose A B
  use SELF
  intro w

  have hA : A.haltsWithOutput w descB := F.printTM_spec descB w


  have hB_run : B.haltsWithOutput descB (F.combineDesc (F.q descB) (F.encode B)) :=
    hB_spec descB

  have hq : F.q descB = F.encode A := rfl

  have henc : F.combineDesc (F.encode A) (F.encode B) = F.encode SELF :=
    (F.encode_compose A B).symm

  rw [hq] at hB_run
  rw [henc] at hB_run

  exact F.compose_spec A B w descB (F.encode SELF) hA hB_run

/-- A "tape-output" fixed-point witness: a TM `fixedTM` whose output on `input` is
`g input ⟨fixedTM⟩`. This packages the self-referential ability to depend on one's
own code at the tape level, parameterized by an external two-argument map `g`. -/
structure TapeOutputFixedPoint (encode : TMDescription Γ → List Γ) where
  g : List Γ → List Γ → List Γ
  fixedTM : TMDescription Γ
  fixedTM_spec : ∀ (input : List Γ),
    fixedTM.haltsWithOutput input (g input (encode fixedTM))

end SelfReference

namespace TuringMachine

open TuringMachine

/-- An abstract acceptable indexing ("coding") of Turing machines over alphabet `Γ`,
sufficient to formalize the Recursion / Fixed-point theorems and the MIN_TM
unrecognizability proof. It records:
* an index type `TMIndex` with an `encode`/`decode` pair and language assignment;
* a pairing function `pair` on strings;
* an `smn` function with the standard `s-m-n` specification;
* a notion `IsComputable` of computable index transformations, closed under the
  needed operations (composition, applying `smn`, and the diagonal `x ↦ smn x x`);
* `representable`: every computable `h : TMIndex → TMIndex` is "implemented" by
  some index `e₀`, i.e. `languageOf (smn e₀ x) = languageOf (h x)`;
* `languages_beyond_length`: arbitrarily long codes are needed to span all
  languages — there exist indices whose language differs from all shorter ones;
* `recognizable_enumSearch_computable`: a recognizable set of codes plus an
  enumeration witness `t` that strictly increases code-length yields a
  computable `t`. -/
structure TMCoding (Γ : Type) where
  TMIndex : Type
  encode : TMIndex → List Γ
  languageOf : TMIndex → Set (List Γ)
  decode : List Γ → Option TMIndex
  decode_encode : ∀ M : TMIndex, decode (encode M) = some M
  pair : List Γ → List Γ → List Γ
  pair_injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d
  smn : TMIndex → TMIndex → TMIndex
  smn_spec : ∀ (e x : TMIndex) (w : List Γ),
    w ∈ languageOf (smn e x) ↔ (pair w (encode x)) ∈ languageOf e
  IsComputable : (TMIndex → TMIndex) → Prop
  representable : ∀ (h : TMIndex → TMIndex), IsComputable h →
    ∃ e : TMIndex, ∀ x : TMIndex,
      languageOf (smn e x) = languageOf (h x)
  isComputable_smn_diag : IsComputable (fun x => smn x x)
  isComputable_comp : ∀ (f g : TMIndex → TMIndex),
    IsComputable f → IsComputable g → IsComputable (f ∘ g)
  isComputable_smn_apply : ∀ (e : TMIndex), IsComputable (smn e)
  languages_beyond_length : ∀ n : ℕ, ∃ M : TMIndex,
    ∀ M' : TMIndex, (encode M').length < n → languageOf M' ≠ languageOf M
  recognizable_enumSearch_computable :
    ∀ (P : TMIndex → Prop),
      IsTuringRecognizable {s : List Γ | ∃ M : TMIndex, encode M = s ∧ P M} →
      ∀ (t : TMIndex → TMIndex),
        (∀ M, P (t M) ∧ (encode M).length < (encode (t M)).length) →
        IsComputable t

/-- **Recursion Theorem** (language form). For any computable transformation
`t : TMIndex → TMIndex` of TM indices, there exists `R` whose language equals the
language of `t R`. This is the language-level avatar of Sipser's statement that for
any TM `T` there is a TM `R` such that `R` on `w` behaves like `T` on `⟨w, R⟩`. -/
theorem recursion_theorem {Γ : Type}
    (C : TMCoding Γ)
    (t : C.TMIndex → C.TMIndex)
    (ht : C.IsComputable t)
    : ∃ R : C.TMIndex, C.languageOf R = C.languageOf (t R) := by

  let h : C.TMIndex → C.TMIndex := fun x => t (C.smn x x)

  have hh : C.IsComputable h :=
    C.isComputable_comp t (fun x => C.smn x x) ht C.isComputable_smn_diag


  obtain ⟨e₀, he₀⟩ := C.representable h hh

  let R := C.smn e₀ e₀

  refine ⟨R, ?_⟩

  exact he₀ e₀

/-- **Fixed-point Theorem** (Sipser, Lecture 11, Ex 2). For any computable
function `f : Σ* → Σ*` (with codomain landing in valid encodings), there is a TM
`R` and a TM `S` with `f(⟨R⟩) = ⟨S⟩` and `L(R) = L(S)`. In other words, every
computable transformation on TM descriptions has a "fixed point" up to language
equality. -/
theorem fixed_point_theorem
    (C : TMCoding Γ)
    (f : List Γ → List Γ)
    (_hf : IsComputableFunction f)
    (hf_maps_to_valid : ∀ M : C.TMIndex,
      ∃ S : C.TMIndex, C.decode (f (C.encode M)) = some S)
    (ht_computable : ∀ (t : C.TMIndex → C.TMIndex),
      (∀ M, C.decode (f (C.encode M)) = some (t M)) → C.IsComputable t)
    : ∃ R : C.TMIndex, ∃ S : C.TMIndex,
        C.decode (f (C.encode R)) = some S ∧
        C.languageOf R = C.languageOf S := by


  classical
  let t : C.TMIndex → C.TMIndex := fun M => (hf_maps_to_valid M).choose
  have ht : ∀ M, C.decode (f (C.encode M)) = some (t M) :=
    fun M => (hf_maps_to_valid M).choose_spec

  obtain ⟨R, hR⟩ := recursion_theorem C t (ht_computable t ht)

  exact ⟨R, t R, ht R, hR⟩

section ComputableQ

variable {Γ : Type} [DecidableEq Γ]

/-- `PrintsAndHalts M w` says: started on the empty tape, `M` reaches an accept
configuration after some `n` steps, with cells `0, …, |w|-1` holding the symbols
of `w` and everywhere else the blank symbol. Captures "M halts having printed
exactly `w`". -/
def PrintsAndHalts {Q : Type} [DecidableEq Q] (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput [] n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput [] n).tape (j : ℤ) = w[j]'hj) ∧
    (∀ i : ℤ, (i < 0 ∨ (w.length : ℤ) ≤ i) →
      (M.runOnInput [] n).tape i = M.blank)

/-- Same as `PrintsAndHalts` but starting from an arbitrary `input` instead of
the blank tape: after some `n` steps `M` accepts and the first `|w|` tape cells
contain `w`. -/
def PrintsAndHaltsOnInput {Q : Type} [DecidableEq Q] (M : TM Q Γ)
    (input w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput input n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput input n).tape (j : ℤ) = w[j]'hj)

/-- The concrete *printer-machine* `P_w` for a string `w`: a TM with `|w| + 2`
states (one per character, plus an accept and a reject state) that on any input
writes `w[0], w[1], …, w[|w|-1]` left-to-right and accepts. This is the explicit
construction underlying the computable function `q(w) = ⟨P_w⟩`. -/
noncomputable def printTM (blank : Γ) (inputAlpha : Set Γ) (h_blank : blank ∉ inputAlpha)
    (w : List Γ) : TM (Fin (w.length + 2)) Γ where
  blank := blank
  inputAlpha := inputAlpha
  blank_not_in_inputAlpha := h_blank
  δ := fun q _ =>
    if hq : q.val < w.length then
      (⟨q.val + 1, by omega⟩, w[q.val]'hq, Direction.R)
    else (q, blank, Direction.R)
  q₀ := ⟨0, by omega⟩
  qAccept := ⟨w.length, by omega⟩
  qReject := ⟨w.length + 1, by omega⟩
  qReject_ne_qAccept := by simp

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
/-- Key loop invariant of `printTM`: after `k ≤ |w|` steps on any `input`, the
machine is in state `k`, the head is at position `k`, and tape cells
`0, …, k-1` already hold the first `k` symbols of `w`. Proved by induction on
`k`. -/
theorem printTM_invariant_any_input (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w : List Γ) (input : List Γ)
    (k : ℕ) (hk : k ≤ w.length) :
    ((printTM blank inputAlpha h_blank w).runOnInput input k).state = ⟨k, by omega⟩ ∧
    ((printTM blank inputAlpha h_blank w).runOnInput input k).headPos = (k : ℤ) ∧
    (∀ (j : ℕ) (hj : j < k),
      ((printTM blank inputAlpha h_blank w).runOnInput input k).tape (j : ℤ) =
        w[j]'(by omega)) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, fun j hj => absurd hj (by omega)⟩
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
  | succ k ih =>
    have hk' : k ≤ w.length := by omega
    obtain ⟨hstate, hhead, htape_w⟩ := ih hk'
    have hk_lt : k < w.length := by omega
    set ck := (printTM blank inputAlpha h_blank w).runOnInput input k with hck_def
    have hrun_succ : (printTM blank inputAlpha h_blank w).runOnInput input (k + 1) =
        (printTM blank inputAlpha h_blank w).step ck := by
      simp [TM.runOnInput, TM.run, hck_def]
    have h_not_halt : ¬(ck.state = (printTM blank inputAlpha h_blank w).qAccept ∨
        ck.state = (printTM blank inputAlpha h_blank w).qReject) := by
      simp only [hstate, printTM, Fin.mk.injEq]; omega
    have hstep_def : (printTM blank inputAlpha h_blank w).step ck =
        ⟨⟨k + 1, by omega⟩, (k : ℤ) + 1, Function.update ck.tape (k : ℤ) (w[k]'hk_lt)⟩ := by
      unfold TM.step
      simp only [h_not_halt, ite_false]
      simp only [printTM, hstate, dif_pos hk_lt, hhead]
    rw [hrun_succ, hstep_def]
    refine ⟨rfl, ?_, ?_⟩
    · norm_cast
    · intro j hj
      simp only [Function.update]
      split_ifs with heq
      · have : j = k := by omega
        subst this; rfl
      · exact htape_w j (by omega)

set_option maxHeartbeats 800000 in
/-- Correctness of `printTM`: on any input, after exactly `|w|` steps the printer
machine `P_w` halts (in fact accepts) and the first `|w|` tape cells (read off by
`Config.readTape`) spell out `w`. This realizes the `haltsWithOutput` spec
demanded by `TMEncoding`. -/
theorem printTM_haltsWithOutput (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w input : List Γ) :
    ∃ n : ℕ,
      (printTM blank inputAlpha h_blank w).isHaltConfig
        ((printTM blank inputAlpha h_blank w).runOnInput input n) ∧
      Config.readTape ((printTM blank inputAlpha h_blank w).runOnInput input n) w.length = w := by
  have hinv := printTM_invariant_any_input blank inputAlpha h_blank w input w.length le_rfl
  refine ⟨w.length, ?_, ?_⟩
  ·
    left
    simp only [TM.isAcceptConfig, printTM]
    exact hinv.1
  ·
    simp only [Config.readTape]
    have hlen : (List.range w.length).length = w.length := List.length_range
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range]
      exact hinv.2.2 i hi1

/-- Abstract form of the textbook Lemma: from any `TMEncoding enc` we get a
computable function `q : Σ* → Σ*` with `q(w) = ⟨P_w⟩`, where `P_w` is a TM that on
every input halts with `w` on the tape. -/
theorem computable_q_is_computable {Γ : Type} (enc : SelfReference.TMEncoding Γ) :
    ∃ q : List Γ → List Γ,
      IsComputableFunction q ∧
      ∀ w, ∃ (Pw : SelfReference.TMDescription Γ),
        q w = enc.encode Pw ∧ ∀ input, Pw.haltsWithOutput input w := by

  refine ⟨fun w => enc.encode (enc.printTMDesc w), enc.q_computable, fun w => ?_⟩
  exact ⟨enc.printTMDesc w, rfl, enc.printTMDesc_spec w⟩

/-- A concrete instance of `TMEncoding` built from the explicit `printTM`
construction. The encoding of a description is taken to be its stored `source`
field, and `printTMDesc w` packages the `printTM w` machine together with
`source := w`, so `q(w) = encode(printTMDesc w) = w` is the identity, which is
clearly computable. -/
noncomputable def concreteTMEncoding (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) : SelfReference.TMEncoding Γ where
  encode := fun desc => desc.source
  printTMDesc := fun w =>
    { Q := Fin (w.length + 2)
      decEq := inferInstance
      machine := printTM blank inputAlpha h_blank w
      source := w }
  printTMDesc_spec := fun w input => by
    simp only [SelfReference.TMDescription.haltsWithOutput]
    exact printTM_haltsWithOutput blank inputAlpha h_blank w input
  q_computable := by


    show IsComputableFunction (fun w => w)
    refine ⟨Fin 2, inferInstance, {
      blank := blank
      inputAlpha := inputAlpha
      blank_not_in_inputAlpha := h_blank
      δ := fun _ a => (⟨0, by omega⟩, a, Direction.R)
      q₀ := ⟨0, by omega⟩
      qAccept := ⟨0, by omega⟩
      qReject := ⟨1, by omega⟩
      qReject_ne_qAccept := by simp
    }, fun w => ?_⟩


    refine ⟨0, ?_, ?_⟩
    ·
      left
      simp [TM.runOnInput, TM.run, TM.initConfig, TM.isAcceptConfig]
    ·
      simp only [TM.runOnInput, TM.run, TM.initConfig, Config.readTape]
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range]
        have h_cond : (0 : ℤ) ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) < (w.length : ℤ) := by
          constructor <;> omega
        rw [dif_pos h_cond]
        simp [Int.toNat_natCast]

set_option linter.unusedSectionVars false in
/-- **Lemma (Computable function q)** (Sipser, Lecture 11): instantiated with
the concrete encoding. There is a computable `q : Σ* → Σ*` such that for every
`w` the description `P_w := printTMDesc w` satisfies `q w = ⟨P_w⟩` and on any
input `P_w` halts with `w` on the tape. -/
theorem computable_q (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) :
    ∃ q : List Γ → List Γ,
      IsComputableFunction q ∧
      ∀ w, ∃ (Pw : SelfReference.TMDescription Γ),
        q w = (concreteTMEncoding blank inputAlpha h_blank).encode Pw ∧
        ∀ input, Pw.haltsWithOutput input w :=
  computable_q_is_computable (concreteTMEncoding blank inputAlpha h_blank)

end ComputableQ

section MinTMUnrecognizable

variable {Γ : Type}

/-- Minimality in the `TMCoding` setting: `M` is minimal if no strictly
shorter-coded index `M'` has the same language. -/
def IsMinimalIndex (C : TMCoding Γ) (M : C.TMIndex) : Prop :=
  ∀ M' : C.TMIndex,
    (C.encode M').length < (C.encode M).length → C.languageOf M' ≠ C.languageOf M

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}` expressed in the `TMCoding` framework. -/
def MIN_TM_Coding (C : TMCoding Γ) : Set (List Γ) :=
  {s | ∃ M : C.TMIndex, C.encode M = s ∧ IsMinimalIndex C M}

/-- Every TM index `M` has a *minimal* equivalent: there exists `M'` with the
same language as `M` such that `M'` is minimal. Proved by strong induction on the
code-length, descending to a shorter equivalent whenever `M` itself is not
minimal. -/
lemma exists_minimal_for_language (C : TMCoding Γ) (M : C.TMIndex) :
    ∃ M' : C.TMIndex, C.languageOf M' = C.languageOf M ∧ IsMinimalIndex C M' := by
  classical
  have : ∀ k : ℕ, ∀ N : C.TMIndex, (C.encode N).length = k →
      ∃ M' : C.TMIndex, C.languageOf M' = C.languageOf N ∧ IsMinimalIndex C M' := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro N hNk
      by_cases hmin : IsMinimalIndex C N
      · exact ⟨N, rfl, hmin⟩
      ·
        unfold IsMinimalIndex at hmin
        push Not at hmin
        obtain ⟨N', hN'_short, hN'_lang⟩ := hmin
        have hN'_len : (C.encode N').length < k := hNk ▸ hN'_short
        obtain ⟨M', hM'_lang, hM'_min⟩ := ih (C.encode N').length hN'_len N' rfl
        exact ⟨M', hM'_lang.trans hN'_lang, hM'_min⟩
  exact this (C.encode M).length M rfl

/-- `MIN_TM` contains codes of arbitrarily large length: for every `n` there is a
minimal index `B` with `|⟨B⟩| ≥ n`. Combines `languages_beyond_length` with
`exists_minimal_for_language` (a shorter minimal equivalent could not differ from
all length-`< n` indices). -/
lemma min_tm_has_arbitrarily_long_elements (C : TMCoding Γ) :
    ∀ n : ℕ, ∃ B : C.TMIndex,
      IsMinimalIndex C B ∧ n ≤ (C.encode B).length := by
  intro n

  obtain ⟨M, hM⟩ := C.languages_beyond_length n

  obtain ⟨M', hM'_lang, hM'_min⟩ := exists_minimal_for_language C M

  refine ⟨M', hM'_min, ?_⟩


  by_contra h
  push Not at h
  exact hM M' h (hM'_lang)

/-- Strict version of `min_tm_has_arbitrarily_long_elements`: for every `n` some
minimal index `B` has `|⟨B⟩| > n`. -/
lemma min_tm_arbitrarily_long_strict (C : TMCoding Γ) :
    ∀ n : ℕ, ∃ B : C.TMIndex,
      IsMinimalIndex C B ∧ n < (C.encode B).length := by
  intro n
  obtain ⟨B, hB_min, hB_len⟩ := min_tm_has_arbitrarily_long_elements C (n + 1)
  exact ⟨B, hB_min, by omega⟩

/-- **MIN_TM is T-unrecognizable** (Sipser, Lecture 11, Ex 3). The language of
codes of minimal Turing machines is not Turing-recognizable. The proof is by
contradiction via the Recursion Theorem: if `MIN_TM` were recognizable, an
enumeration would produce a computable map `t` sending each `M` to a *strictly
longer* minimal machine, but then any fixed point `R` of `t` from the Recursion
Theorem (with `L(R) = L(t R)`) would witness `t R` not being minimal — a
contradiction. -/
theorem MIN_TM_not_recognizable (C : TMCoding Γ) :
    ¬ IsTuringRecognizable (MIN_TM_Coding C) := by
  intro hRec
  have h_inf := min_tm_arbitrarily_long_strict C
  classical
  let t : C.TMIndex → C.TMIndex := fun M => (h_inf (C.encode M).length).choose
  have ht_spec : ∀ M, IsMinimalIndex C (t M) ∧
      (C.encode M).length < (C.encode (t M)).length :=
    fun M => (h_inf (C.encode M).length).choose_spec
  have ht_comp : C.IsComputable t :=
    C.recognizable_enumSearch_computable (IsMinimalIndex C) hRec t ht_spec
  obtain ⟨R, hR⟩ := recursion_theorem C t ht_comp
  exact (ht_spec R).1 R (ht_spec R).2 hR

end MinTMUnrecognizable

end TuringMachine

namespace TuringMachine

open TuringMachine

/-- A `TMCoding` augmented with a computable "complement" operation `compl`
mapping each index `M` to an index whose language is the set complement of
`L(M)`. Useful for applying the Recursion Theorem to constructions that flip
acceptance. -/
structure TMCodingWithCompl (Γ : Type) where
  coding : TMCoding Γ
  compl : coding.TMIndex → coding.TMIndex
  compl_spec : ∀ M : coding.TMIndex, coding.languageOf (compl M) = (coding.languageOf M)ᶜ
  compl_computable : coding.IsComputable compl

/-- **A_TM is undecidable — new proof via the Recursion Theorem** (Sipser,
Lecture 11, Ex 1). Suppose `H` decided `A_TM`. Let `D` be `H` with its accept and
reject states swapped (so `D` decides the complement of `A_TM`). By the
self-reference property of `enc`, there is a description `d₀` whose computation
behaves like running `D` on `⟨d₀⟩`, giving `d₀.accepts ↔ ¬ d₀.accepts`,
contradiction. -/
theorem A_TM_not_decidable_via_recursion_theorem
    (enc : TMEncoding Γ) :
    ¬IsTuringDecidable (A_TM enc) := by

  intro ⟨QH, decEqH, H, hDecider, hLang⟩


  have hH_iff : ∀ d : TMDesc Γ,
      @TM.accepts QH Γ decEqH H (enc.encode d) ↔ d.accepts := by
    intro d
    have hLang' : ∀ w, @TM.accepts QH Γ decEqH H w ↔ w ∈ A_TM enc := by
      intro w
      change w ∈ @TM.language QH Γ decEqH H ↔ w ∈ A_TM enc
      rw [hLang]
    rw [hLang' (enc.encode d)]
    constructor
    · rintro ⟨d', henc, hacc⟩
      exact enc.encode_injective henc ▸ hacc
    · intro hacc
      exact ⟨d, rfl, hacc⟩


  let D := @TM.flip QH Γ decEqH H
  have hD : ∀ w, @TM.accepts QH Γ decEqH D w ↔
      ¬ @TM.accepts QH Γ decEqH H w :=
    TM.flip_accepts_iff H hDecider


  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef D


  have hcontra : d₀.accepts ↔ ¬ d₀.accepts := by
    calc d₀.accepts
        ↔ @TM.accepts QH Γ decEqH D (enc.encode d₀) := hSelfRef
      _ ↔ ¬ @TM.accepts QH Γ decEqH H (enc.encode d₀) := hD _
      _ ↔ ¬ d₀.accepts := not_congr (hH_iff d₀)

  by_cases h : d₀.accepts
  · exact hcontra.mp h h
  · exact h (hcontra.mpr h)

end TuringMachine

namespace GodelIncompleteness

open TuringMachine

/-- The complement `\overline{A_{TM}}` of the acceptance language `A_TM`. This
language is famously *not* Turing-recognizable and is the one whose
"unprovability" gives Gödel-style results in this development. -/
def A_TM_complement (enc : TMEncoding Γ) : Set (List Γ) :=
  (A_TM enc)ᶜ

/-- A minimal abstract "formal proof system" over a TM-encoding `enc`. It picks
out a Turing-recognizable set `provable ⊆ Σ*` of provable statements about TM
descriptions, with the soundness assumption that if `⟨d⟩ ∈ provable` then `d`
does *not* accept (the statement "`d` is non-accepting" is true). -/
structure FormalProofSystem (Γ : Type) where
  enc : TMEncoding Γ
  provable : Set (List Γ)
  sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts
  provable_recognizable : IsTuringRecognizable provable

/-- A `FormalProofSystem` is *complete* if every true non-acceptance statement
is provable: whenever `d` does not accept, `⟨d⟩ ∈ provable`. Gödel's
First Incompleteness Theorem says no sound, recognizable system can be complete
in this sense. -/
def FormalProofSystem.isComplete {Γ : Type} (F : FormalProofSystem Γ) : Prop :=
  ∀ (d : TMDesc Γ), ¬d.accepts → F.enc.encode d ∈ F.provable

/-- **Gödel's First Incompleteness Theorem** (Sipser, Lecture 11). For any sound
proof system whose set of provable statements about TMs is Turing-recognizable,
there is a true statement that is unprovable: there exists a description `d`
such that `d` does not accept (true statement) yet `⟨d⟩ ∉ provable`.

The proof uses the self-reference property of the encoding `enc` to build `d₀`
whose machine effectively simulates the recognizer `P` of `provable` on `⟨d₀⟩`;
soundness then forces `d₀` to be non-accepting and unprovable. -/
theorem godel_first_incompleteness
    {Γ : Type} (enc : TMEncoding Γ)

    (provable : Set (List Γ))
    (h_provable_recognizable : IsTuringRecognizable provable)

    (h_sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts)
    : ∃ (d : TMDesc Γ), ¬d.accepts ∧ enc.encode d ∉ provable := by


  obtain ⟨QP, decEqP, P, hP⟩ := h_provable_recognizable

  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef P
  refine ⟨d₀, ?_, ?_⟩
  ·
    intro hAccepts
    have hPAccepts := hSelfRef.mp hAccepts
    have hProvable : enc.encode d₀ ∈ provable := by rw [← hP]; exact hPAccepts
    exact h_sound d₀ hProvable hAccepts
  ·
    intro hProvable
    have hNotAccepts := h_sound d₀ hProvable
    have hPAccepts : @TM.accepts QP Γ decEqP P (enc.encode d₀) := by
      rw [← hP] at hProvable; exact hProvable
    exact hNotAccepts (hSelfRef.mpr hPAccepts)

/-- **A True but Unprovable Statement** (Sipser, Lecture 11). Concrete version
of Gödel's theorem: given an explicit TM `P` whose language is `provable` and
soundness of `provable`, there is a description `d₀` such that (1) `d₀` does not
accept (the statement `⟨d₀⟩ ∈ \overline{A_{TM}}` is true) and (2)
`⟨d₀⟩ ∉ provable` (it has no proof). The witness `d₀` corresponds to Sipser's
machine `R` which on any input obtains its own code, forms the statement
`φ_U = "⟨R, 0⟩ ∈ \overline{A_{TM}}"`, and searches for a proof of `φ_U`. -/
theorem true_but_unprovable_statement
    {Γ : Type} (enc : TMEncoding Γ)
    (provable : Set (List Γ))

    (h_sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts)


    {QP : Type} [DecidableEq QP] (P : TM QP Γ)
    (hP : P.language = provable)
    : ∃ (d : TMDesc Γ), ¬d.accepts ∧ enc.encode d ∉ provable := by


  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef P
  refine ⟨d₀, ?_, ?_⟩
  ·

    intro hAccepts

    have hPAccepts := hSelfRef.mp hAccepts

    have hProvable : enc.encode d₀ ∈ provable := by
      rw [← hP]
      exact hPAccepts

    exact h_sound d₀ hProvable hAccepts
  ·

    intro hProvable

    have hNotAccepts := h_sound d₀ hProvable

    have hPAccepts : @TM.accepts QP Γ _ P (enc.encode d₀) := by
      rw [← hP] at hProvable
      exact hProvable

    exact hNotAccepts (hSelfRef.mpr hPAccepts)

end GodelIncompleteness
