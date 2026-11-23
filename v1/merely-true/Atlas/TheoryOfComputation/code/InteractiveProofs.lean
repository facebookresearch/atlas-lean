/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.BPP
import Atlas.TheoryOfComputation.code.SpaceComplexity
namespace InteractiveProofs

open TuringMachine

/-- A *prover* `P` in an interactive proof system. Given the input `w : List Γ`
and the transcript-so-far (a list of messages already exchanged), `P` returns
the next message to send to the verifier. Provers are not restricted in
computational power. -/
def Prover (Γ : Type) : Type :=
  List Γ → List (List Γ) → List Γ

/-- A *verifier* `V` in an interactive proof system. It is parameterised by a
state-type `Q` and the alphabet `Γ`. On input `w` with `n` random coins
`Fin n → Bool`, it can `sendMessage` to the prover or `decide` (accept/reject)
based on the transcript of the conversation. -/
structure Verifier (Q : Type) (Γ : Type) where
  sendMessage : (w : List Γ) → (n : ℕ) → (Fin n → Bool) → (transcript : List (List Γ)) → List Γ
  decide : (w : List Γ) → (n : ℕ) → (Fin n → Bool) → (transcript : List (List Γ)) → Bool

variable {Q : Type} {Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- Run `k` rounds of interaction between verifier `V` and prover `P` on
input `w` using random coins `coins : Fin n → Bool`. Each round consists of a
verifier message followed by a prover message. Returns the resulting transcript
as a `List (List Γ)`. -/
def runRounds (V : Verifier Q Γ) (P : Prover Γ) (w : List Γ)
    (n : ℕ) (coins : Fin n → Bool) : ℕ → List (List Γ)
  | 0 => []
  | k + 1 =>
    let prevTranscript := runRounds V P w n coins k
    let vMsg := V.sendMessage w n coins prevTranscript
    let transcriptWithVMsg := prevTranscript ++ [vMsg]
    let pMsg := P w transcriptWithVMsg
    prevTranscript ++ [vMsg, pMsg]

/-- The boolean outcome of running the full `numRounds`-round protocol
`V ↔ P` on input `w` with random coins `coins`: returns `true` iff `V` accepts
the resulting transcript. -/
def runProtocol (V : Verifier Q Γ) (P : Prover Γ) (w : List Γ)
    (n : ℕ) (coins : Fin n → Bool) (numRounds : ℕ) : Bool :=
  let transcript := runRounds V P w n coins numRounds
  V.decide w n coins transcript

/-- The number of random-coin assignments in `Fin n → Bool` that lead `V` to
accept when interacting with `P` on input `w` for `numRounds` rounds. -/
def Verifier.numAccepting (V : Verifier Q Γ) (P : Prover Γ)
    (w : List Γ) (n : ℕ) (numRounds : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (coins : Fin n → Bool) =>
    runProtocol V P w n coins numRounds = true))

/-- The acceptance probability `Pr[(V ↔ P) accepts w] =
|accepting coin sequences| / 2ⁿ` over uniformly random coins in `Fin n → Bool`. -/
def Verifier.acceptProb (V : Verifier Q Γ) (P : Prover Γ)
    (w : List Γ) (n : ℕ) (numRounds : ℕ) : ℚ :=
  (V.numAccepting P w n numRounds : ℚ) / ((2 : ℚ) ^ n)

/-- Notation-level alias for the textbook quantity `Pr[(V ↔ P) accepts w]`,
defined as `V.acceptProb P w n numRounds`. -/
def IPAcceptanceProbability (V : Verifier Q Γ) (P : Prover Γ)
    (w : List Γ) (n : ℕ) (numRounds : ℕ) : ℚ :=
  V.acceptProb P w n numRounds

/-- `(V, P)` is an *interactive proof system* for the language `A` with random
budget `t` and round budget `r` if:

* (completeness) for every `w ∈ A`, `Pr[(V ↔ P) accepts w] ≥ 2/3`;
* (soundness) for every `w ∉ A` and every *dishonest* prover `P̃`,
  `Pr[(V ↔ P̃) accepts w] ≤ 1/3`. -/
def IsInteractiveProofSystem (V : Verifier Q Γ) (P : Prover Γ)
    (A : Set (List Γ)) (t : ℕ → ℕ) (r : ℕ → ℕ) : Prop :=

  (∀ w : List Γ, w ∈ A → V.acceptProb P w (t w.length) (r w.length) ≥ 2 / 3) ∧

  (∀ w : List Γ, w ∉ A → ∀ P' : Prover Γ, V.acceptProb P' w (t w.length) (r w.length) ≤ 1 / 3)

/-- The class **IP** (Sipser, Lecture 25): a language `A` is in `IP` if there
exist a verifier `V` and an honest prover `P` such that `(V, P)` forms an
interactive proof system for `A` with both the random-coin budget `t` and the
number-of-rounds budget `r` polynomial in the input length. -/
def InIP {Γ : Type} [DecidableEq Γ] (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (V : Verifier Q Γ) (P : Prover Γ)
    (k : ℕ) (t : ℕ → ℕ) (j : ℕ) (r : ℕ → ℕ),
    IsBigO t (fun n => n ^ k) ∧
    IsBigO r (fun n => n ^ j) ∧
    IsInteractiveProofSystem V P A t r

/-- Predicate saying that every message the verifier `V` sends has length
bounded by `|w|^ℓ + ℓ`, i.e. its outgoing communication is polynomial in the
input length. Used to formulate the *strong* notion `InIP_strong` which is the
form needed for `IP = PSPACE`. -/
def VerifierPolyMessages {Q Γ : Type} (V : Verifier Q Γ) (t : ℕ → ℕ) (ℓ : ℕ) : Prop :=
  ∀ w : List Γ, ∀ (coins : Fin (t w.length) → Bool)
    (transcript : List (List Γ)),
    (V.sendMessage w (t w.length) coins transcript).length ≤ w.length ^ ℓ + ℓ

/-- The *strong* form of IP membership, identical to `InIP` but additionally
requiring that the verifier's outgoing messages have polynomial length
(`VerifierPolyMessages V t ℓ`). This is the formulation used in the standard
`IP = PSPACE` proof. -/
def InIP_strong {Γ : Type} [DecidableEq Γ] (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (V : Verifier Q Γ) (P : Prover Γ)
    (k : ℕ) (t : ℕ → ℕ) (j : ℕ) (r : ℕ → ℕ) (ℓ : ℕ),
    IsBigO t (fun n => n ^ k) ∧
    IsBigO r (fun n => n ^ j) ∧
    VerifierPolyMessages V t ℓ ∧
    IsInteractiveProofSystem V P A t r

/-- Dot-notation alias for `VerifierPolyMessages`: every message sent by `V`
has length at most `|w|^ℓ + ℓ`. -/
def Verifier.PolyMessages {Q Γ : Type} (V : Verifier Q Γ) (t : ℕ → ℕ) (ℓ : ℕ) : Prop :=
  ∀ w : List Γ, ∀ (coins : Fin (t w.length) → Bool)
    (transcript : List (List Γ)),
    (V.sendMessage w (t w.length) coins transcript).length ≤ w.length ^ ℓ + ℓ

end InteractiveProofs

namespace IPEqPSPACE

open InteractiveProofs SpaceComplexity






end IPEqPSPACE

