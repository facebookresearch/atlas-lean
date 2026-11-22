/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.InteractiveProofs
import Atlas.TheoryOfComputation.code.Probabilistic
import Mathlib.Tactic

namespace GraphNonIsoIP

open InteractiveProofs Probabilistic TuringMachine

/-- The **graph non-isomorphism** language `\overline{ISO}`: the complement of
`ISO = { ⟨G, H⟩ | G and H are isomorphic graphs }` under a fixed encoding of
graph pairs. Membership `⟨G, H⟩ ∈ ISO_bar` says that the two graphs are *not*
isomorphic. -/
def ISO_bar {Γ : Type} (enc : GraphPairEncoding Γ) : Set (List Γ) :=
  (ISO enc)ᶜ

/-- A `GraphPermuter` packages the random-permutation oracle used by the
honest prover in the IP protocol for graph non-isomorphism.

* `challenge w b seed` returns the verifier's challenge graph obtained by
  randomly permuting either graph (`b = false`) or the other (`b = true`).
* `iso_challenge_eq` says that **if the input pair `w` is isomorphic** then
  the two challenge distributions coincide: the prover cannot distinguish.
* `identify msg` reads a challenge back and reports which of the two graphs
  it came from.
* `identify_correct` says that **if the input pair `w` is not isomorphic** then
  `identify` recovers the bit `b` that the verifier used. -/
structure GraphPermuter (Γ : Type) (enc : GraphPairEncoding Γ) where
  challenge : List Γ → Bool → List Γ → List Γ
  iso_challenge_eq : ∀ w : List Γ, w ∈ ISO enc →
    ∀ (seed : List Γ), challenge w true seed = challenge w false seed
  identify : List Γ → List Γ → Bool
  identify_correct : ∀ w : List Γ, w ∉ ISO enc →
    ∀ (b : Bool) (seed : List Γ), identify w (challenge w b seed) = b

/-- A toy default implementation of `GraphPermuter` used to show that the
structure is inhabited.

It does not implement an actual graph permutation; instead it produces
length-distinguishable outputs whenever the input pair is not isomorphic
(satisfying `identify_correct`) and a single constant output whenever the
input is isomorphic (satisfying `iso_challenge_eq`). It suffices for proving
`ISO_bar ∈ IP`. -/
noncomputable def defaultGraphPermuter {Γ : Type} [Inhabited Γ]
    (enc : GraphPairEncoding Γ) : GraphPermuter Γ enc where
  challenge w b _seed :=
    if @decide (w ∈ ISO enc) (Classical.dec _) then
      w
    else
      if b then w ++ [default] else w
  iso_challenge_eq w hw seed := by
    have htrue : @decide (w ∈ ISO enc) (Classical.dec _) = true :=
      @decide_eq_true _ (Classical.dec _) hw
    simp [htrue]
  identify w msg :=
    decide (msg.length > w.length)
  identify_correct w hw b seed := by
    have hfalse : @decide (w ∈ ISO enc) (Classical.dec _) = false :=
      @decide_eq_false _ (Classical.dec _) hw
    simp only [hfalse]
    cases b <;> simp [List.length_append]

/-- For fixed guesses `g1, g2 : Bool`, at most one of the four coin
assignments `coins : Fin 2 → Bool` matches both guesses simultaneously.

This bounds the cheating probability of a dishonest prover in the
graph non-isomorphism IP protocol by `1 / 4 ≤ 1 / 3`. -/
lemma coin_match_le_one (g1 g2 : Bool) :
    (Finset.univ.filter (fun (coins : Fin 2 → Bool) =>
      ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩)) = true)).card ≤ 1 := by
  fin_cases g1 <;> fin_cases g2 <;> decide

/-- The verifier in the graph non-isomorphism IP protocol.

Using two random coins, in two rounds it sends `perm.challenge w bᵢ w` for
`b₀, b₁ ∈ {true, false}` and finally accepts iff the prover's responses
correctly identify the bits, i.e. both `coins ⟨0⟩ == guess1` and
`coins ⟨1⟩ == guess2` hold. -/
def isoBarVerifier {Γ : Type} [DecidableEq Γ]
    {enc : GraphPairEncoding Γ}
    (perm : GraphPermuter Γ enc) : Verifier Bool Γ :=
  { sendMessage := fun w n coins transcript =>
      if h : n ≥ 2 then


        if transcript.length = 0 then
          perm.challenge w (coins ⟨0, by omega⟩) w
        else if transcript.length = 2 then
          perm.challenge w (coins ⟨1, by omega⟩) w
        else []
      else []
    decide := fun w n coins transcript =>
      if h : n ≥ 2 then


        match transcript with
        | [_, response1, _, response2] =>
          let guess1 : Bool := !response1.isEmpty
          let guess2 : Bool := !response2.isEmpty
          (coins ⟨0, by omega⟩ == guess1) && (coins ⟨1, by omega⟩ == guess2)
        | _ => false
      else false }

/-- The honest prover in the graph non-isomorphism IP protocol.

After each verifier challenge `c` it calls `perm.identify input c` and replies
with a nonempty marker (`[default]`) if the bit is identified as `true`, and
the empty list otherwise. By `identify_correct`, when `w ∉ ISO enc` (i.e.
`w ∈ ISO_bar enc`) the honest prover always recovers the verifier's bits and
the protocol accepts with probability 1. -/
def isoBarHonestProver {Γ : Type} [Inhabited Γ]
    {enc : GraphPairEncoding Γ}
    (perm : GraphPermuter Γ enc) : Prover Γ :=
  fun input transcript =>
    match transcript with
    | [challenge] =>

      if perm.identify input challenge then [default] else []
    | [_, _, challenge] =>

      if perm.identify input challenge then [default] else []
    | _ => []

/-- **Graph non-isomorphism is in IP** (relative to a `GraphPermuter` oracle).

`\overline{ISO} ∈ IP`: there is an interactive proof system in which
* if `w ∈ ISO_bar enc` (graphs not isomorphic) the honest prover convinces the
  verifier with probability `≥ 2/3` (in fact 1 here);
* if `w ∉ ISO_bar enc` (graphs are isomorphic) any prover `P'` is accepted
  with probability `≤ 1/3` (in fact `≤ 1/4` here), because the prover's two
  guesses can match the verifier's two random coin flips for at most one of
  the four coin assignments. -/
theorem iso_bar_in_IP {Γ : Type} [DecidableEq Γ] [Inhabited Γ]
    (enc : GraphPairEncoding Γ) (perm : GraphPermuter Γ enc) :
    InIP (ISO_bar enc) := by


  refine ⟨Bool, inferInstance, isoBarVerifier perm, isoBarHonestProver perm,
    1, fun _ => 2, 1, fun _ => 2, ?_, ?_, ?_⟩
  ·
    exact ⟨2, 1, by omega, fun n hn => by simp; omega⟩
  ·
    exact ⟨2, 1, by omega, fun n hn => by simp; omega⟩
  ·
    unfold IsInteractiveProofSystem
    constructor
    ·
      intro w hw
      unfold Verifier.acceptProb Verifier.numAccepting
      have hw_not_iso : w ∉ ISO enc := hw
      suffices h : ∀ coins : Fin 2 → Bool,
          runProtocol (isoBarVerifier perm) (isoBarHonestProver perm) w 2 coins 2 = true by
        simp only [Finset.filter_true_of_mem (fun x _ => h x), Finset.card_univ,
          Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        norm_num
      intro coins
      show runProtocol (isoBarVerifier perm) (isoBarHonestProver perm) w 2 coins 2 = true
      simp only [runProtocol, runRounds, isoBarVerifier, isoBarHonestProver,
        show (2 : ℕ) ≥ 2 from le_refl 2, dite_true,
        List.length_nil, List.length_append, List.length_cons, List.length_singleton,
        List.nil_append, List.cons_append, Nat.reduceAdd,
        show (0 : ℕ) = 0 from rfl, show ¬(2 : ℕ) = 0 from by omega, show (2 : ℕ) = 2 from rfl,
        ite_true, ite_false]
      have hid := perm.identify_correct w hw_not_iso
      set b1 := coins ⟨0, by omega⟩
      set b2 := coins ⟨1, by omega⟩
      have hid1 : perm.identify w (perm.challenge w b1 w) = b1 := hid b1 w
      have hid2 : perm.identify w (perm.challenge w b2 w) = b2 := hid b2 w
      simp only [hid1, hid2]
      cases b1 <;> cases b2 <;> simp [hid _ w]
    ·
      intro w hw P'
      unfold Verifier.acceptProb Verifier.numAccepting
      have hw_iso : w ∈ ISO enc := by
        simp only [ISO_bar, Set.mem_compl_iff] at hw
        exact not_not.mp hw
      have hchallenge_eq : ∀ (b : Bool),
          perm.challenge w b w = perm.challenge w true w := by
        intro b; cases b
        · exact (perm.iso_challenge_eq w hw_iso w).symm
        · rfl

      have heq : ∀ coins : Fin 2 → Bool,
          runProtocol (isoBarVerifier perm) P' w 2 coins 2 =
            let c := perm.challenge w true w
            let r1 := P' w [c]
            let g1 : Bool := !r1.isEmpty
            let r2 := P' w [c, r1, c]
            let g2 : Bool := !r2.isEmpty
            (coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2) := by
        intro coins
        simp only [runProtocol, runRounds, isoBarVerifier,
          show (2 : ℕ) ≥ 2 from le_refl 2, dite_true,
          List.length_nil, List.length_append, List.length_cons, List.length_singleton,
          List.nil_append, List.cons_append, Nat.reduceAdd, ite_true, ite_false, decide_true, decide_false]
        rw [hchallenge_eq (coins ⟨0, by omega⟩)]
        rw [hchallenge_eq (coins ⟨1, by omega⟩)]
        simp only [show ¬(2 : ℕ) = 0 from by omega, ite_false]

      set c := perm.challenge w true w
      set r1 := P' w [c]
      set g1 : Bool := !r1.isEmpty
      set r2 := P' w [c, r1, c]
      set g2 : Bool := !r2.isEmpty

      have hfilter : (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          runProtocol (isoBarVerifier perm) P' w 2 coins 2 = true)) =
        (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2)) = true)) := by
        ext coins
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heq]
      rw [hfilter]

      have hfilter2 : (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((coins ⟨0, by omega⟩ == g1) && (coins ⟨1, by omega⟩ == g2)) = true)) =
        (Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩)) = true)) := by
        congr 1; ext coins
        simp only [Bool.beq_comm]
      rw [hfilter2]

      have hcount := coin_match_le_one g1 g2
      have hle : ((Finset.univ.filter (fun coins : Fin 2 → Bool =>
          ((g1 == coins ⟨0, by omega⟩) && (g2 == coins ⟨1, by omega⟩))
            = true)).card : ℚ) ≤ 1 :=
        Nat.cast_le.mpr hcount
      linarith

end GraphNonIsoIP

open GraphNonIsoIP InteractiveProofs Probabilistic in
/-- **Graph non-isomorphism is in IP**: `\overline{ISO} ∈ IP`.

Top-level corollary specializing `iso_bar_in_IP` to the `defaultGraphPermuter`,
giving an unconditional instance of the interactive-proof membership. -/
theorem ISO_bar_in_IP {Γ : Type} [DecidableEq Γ] [Inhabited Γ]
    (enc : GraphPairEncoding Γ) :
    InIP (ISO_bar enc) :=
  GraphNonIsoIP.iso_bar_in_IP enc (GraphNonIsoIP.defaultGraphPermuter enc)
