/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log

namespace PCP

abbrev BinaryString (n : ℕ) := Fin n → Bool

def Language := ∀ (n : ℕ), Set (BinaryString n)

def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ n, f n ≤ c * n ^ k + c

structure NPVerifier (n : ℕ) (witnessLen : ℕ) where
  decide : BinaryString n → BinaryString witnessLen → Bool

def InNP (L : Language) : Prop :=
  ∃ (p : ℕ → ℕ), IsPolynomial p ∧ ∀ (n : ℕ), ∃ (V : NPVerifier n (p n)),
    (∀ (x : BinaryString n), x ∈ L n →
      ∃ (w : BinaryString (p n)), V.decide x w = true) ∧
    (∀ (x : BinaryString n), x ∉ L n →
      ∀ (w : BinaryString (p n)), V.decide x w = false)

structure PCPVerifier (n : ℕ) where
  numRandom : ℕ
  numQueries : ℕ
  proofLen : ℕ
  queryPositions : BinaryString numRandom → Fin numQueries → Fin proofLen
  decide : BinaryString n → BinaryString numRandom → BinaryString numQueries → Bool

def PCPVerifier.accepts {n : ℕ} (V : PCPVerifier n) (x : BinaryString n)
    (π : BinaryString V.proofLen) (r : BinaryString V.numRandom) : Bool :=
  let queriedBits : BinaryString V.numQueries := fun i => π (V.queryPositions r i)
  V.decide x r queriedBits

def PCPVerifier.hasCompleteness {n : ℕ} (V : PCPVerifier n) (L : Language)  : Prop :=
  ∀ (x : BinaryString n), x ∈ L n →
    ∃ (π : BinaryString V.proofLen), ∀ (r : BinaryString V.numRandom),
      V.accepts x π r = true

def PCPVerifier.hasSoundness {n : ℕ} (V : PCPVerifier n) (L : Language) (s : ℝ) : Prop :=
  ∀ (x : BinaryString n), x ∉ L n →
    ∀ (π : BinaryString V.proofLen),
      ((Finset.univ.filter (fun r => V.accepts x π r = true)).card : ℝ) ≤
        s * (2 : ℝ) ^ V.numRandom

def IsOLogN (f : ℕ → ℕ) : Prop :=
  ∃ (c c' : ℕ), ∀ n, f n ≤ c * Nat.log 2 n + c'

def IsO1 (f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ), ∀ n, f n ≤ c

def InPCP (L : Language) (rBound : (ℕ → ℕ) → Prop) (qBound : (ℕ → ℕ) → Prop) : Prop :=
  ∃ (r q : ℕ → ℕ), rBound r ∧ qBound q ∧
    ∃ (s : ℝ), s < 1 ∧
      ∀ (n : ℕ), ∃ (V : PCPVerifier n),
        V.numRandom = r n ∧ V.numQueries = q n ∧
        V.hasCompleteness L ∧ V.hasSoundness L s

structure Literal (n : ℕ) where
  var : Fin n
  polarity : Bool

structure Clause (n : ℕ) where
  lit₁ : Literal n
  lit₂ : Literal n
  lit₃ : Literal n

abbrev Assignment (n : ℕ) := Fin n → Bool

def Literal.satisfiedBy {n : ℕ} (l : Literal n) (σ : Assignment n) : Bool :=
  σ l.var == l.polarity

def Clause.satisfiedBy {n : ℕ} (c : Clause n) (σ : Assignment n) : Bool :=
  c.lit₁.satisfiedBy σ || c.lit₂.satisfiedBy σ || c.lit₃.satisfiedBy σ

structure ThreeSATFormula where
  numVars : ℕ
  clauses : List (Clause numVars)
  clauses_nonempty : clauses ≠ []

def numSatisfied (φ : ThreeSATFormula) (σ : Assignment φ.numVars) : ℕ :=
  (φ.clauses.filter (·.satisfiedBy σ = true)).length

def IsSatisfiable (φ : ThreeSATFormula) : Prop :=
  ∃ σ : Assignment φ.numVars, ∀ c ∈ φ.clauses, c.satisfiedBy σ = true

def HasMaxSatFractionAtMost (φ : ThreeSATFormula) (s : ℝ) : Prop :=
  ∀ σ : Assignment φ.numVars, (numSatisfied φ σ : ℝ) ≤ s * (φ.clauses.length : ℝ)





end PCP
