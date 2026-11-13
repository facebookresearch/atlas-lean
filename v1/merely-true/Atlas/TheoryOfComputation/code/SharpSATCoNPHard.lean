/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

namespace NPCompleteness

open TuringMachine in
/--
A language `B` is `coNP`-hard if every language `A ∈ coNP` polynomial-time
reduces to `B`. Analogous to the NP-hardness definition `∀ A ∈ NP, A ≤_P B`
from the textbook, but for the class `coNP`.
-/
def IsCoNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InCoNP A → PolyReducible A B

/--
One plus the largest variable index appearing in `φ`. This gives an upper bound
`m` such that every variable of `φ` has index `< m`.
-/
noncomputable def BoolFormula.maxVarSucc (φ : BoolFormula) : ℕ :=
  (φ.vars.sup id).succ

/--
The truth value `φ.eval σ` depends only on the values of `σ` on the variables
that actually occur in `φ`. If two assignments agree on `φ.vars` they yield the
same evaluation.
-/
theorem BoolFormula.eval_eq_of_agree_on_vars
    (φ : BoolFormula) (h : ∀ i ∈ φ.vars, σ₁ i = σ₂ i) :
    φ.eval σ₁ = φ.eval σ₂ := by
  induction φ with
  | var n =>
    simp only [eval]
    exact h n (Finset.mem_singleton.mpr rfl)
  | trueConst => rfl
  | falseConst => rfl
  | not ψ ih =>
    simp only [eval]
    congr 1
    exact ih (fun i hi => h i (by simp [vars]; exact hi))
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [eval]
    congr 1
    · exact ih₁ (fun i hi => h i (by simp [vars]; left; exact hi))
    · exact ih₂ (fun i hi => h i (by simp [vars]; right; exact hi))
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [eval]
    congr 1
    · exact ih₁ (fun i hi => h i (by simp [vars]; left; exact hi))
    · exact ih₂ (fun i hi => h i (by simp [vars]; right; exact hi))

/--
If `φ` is unsatisfiable then its `#SAT` count is zero. One direction of the
equivalence between satisfiability and positive `#SAT` count.
-/
theorem BoolFormula.countSat_eq_zero_of_not_satisfiable {φ : BoolFormula}
    (hunsat : ¬φ.Satisfiable) : φ.countSat = 0 := by
  unfold countSat
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ heval
  exact hunsat ⟨fun i => if h : i ∈ φ.vars then σ ⟨i, h⟩ else false, heval⟩

/--
Converse of `countSat_eq_zero_of_not_satisfiable`: if `φ` has zero satisfying
assignments then `φ` is unsatisfiable.
-/
theorem BoolFormula.not_satisfiable_of_countSat_eq_zero {φ : BoolFormula}
    (hcount : φ.countSat = 0) :
    ¬φ.Satisfiable := by
  intro ⟨σ, hσ⟩
  unfold countSat at hcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcount

  let σ' : φ.vars → Bool := fun ⟨i, _⟩ => σ i
  have hfalse := hcount (Finset.mem_univ σ')
  simp only [Bool.not_eq_true] at hfalse

  have hagree : ∀ i ∈ φ.vars,
      (fun j => if hj : j ∈ φ.vars then σ' ⟨j, hj⟩ else false) i = σ i := by
    intro i hi
    simp [hi, σ']
  rw [φ.eval_eq_of_agree_on_vars hagree] at hfalse
  rw [hσ] at hfalse
  exact Bool.noConfusion hfalse

/-- A Boolean formula `φ` is a tautology iff `φ.eval σ = true` for every
assignment `σ`. -/
def BoolFormula.IsTautology (φ : BoolFormula) : Prop :=
  ∀ σ : BoolAssignment, φ.eval σ = true

/-- The language `TAUTOLOGY = {⟨φ⟩ | φ is a tautology}`, the canonical
coNP-complete language. -/
def TAUTOLOGY : Set BoolFormula :=
  {φ | φ.IsTautology}

open TuringMachine

section CoNPHardness

/--
A simple encoding of `#SAT` instances `⟨φ, k⟩` as lists of Boolean formulas,
specifically tailored for the coNP-hardness reduction. Only one round-trip law
is required: `decode (encode p) = some p`.
-/
structure SharpSATEncoding where
  encode : BoolFormula × ℕ → List BoolFormula
  decode : List BoolFormula → Option (BoolFormula × ℕ)
  decode_encode : ∀ p, decode (encode p) = some p

variable (enc : SharpSATEncoding)

/--
The `#SAT` language as a set of encoded instances over the alphabet
`BoolFormula`: `w` is accepted iff it decodes to a pair `⟨φ, k⟩` with
`k = countSat φ`.
-/
def SharpSATLang : Set (List BoolFormula) :=
  {w | ∃ φ k, enc.decode w = some (φ, k) ∧ k = φ.countSat}

/--
If `Aᶜ ≤_P B` then `A ≤_P Bᶜ` (the same reduction function works in both
directions, since `w ∈ Aᶜ ↔ f(w) ∈ B` is equivalent to `w ∈ A ↔ f(w) ∈ Bᶜ`).
-/
theorem PolyReducible.compl_left {Γ : Type} {A B : Set (List Γ)}
    (h : PolyReducible Aᶜ B) : PolyReducible A Bᶜ := by
  obtain ⟨f, hf_poly, hf_red⟩ := h
  exact ⟨f, hf_poly, fun w => by
    simp only [Set.mem_compl_iff]
    constructor
    · intro hw hfB
      exact ((hf_red w).mpr hfB) hw
    · intro hfnB
      by_contra hwnA
      exact hfnB ((hf_red w).mp hwnA)⟩

/--
The reduction `UNSAT ≤_P #SAT`: given an input encoding a single Boolean
formula `φ` (the natural input format for UNSAT), output the `#SAT` encoding of
`⟨φ, 0⟩`. Malformed inputs are mapped to the encoding of `⟨false, 0⟩` (which is
trivially a true `#SAT` instance, but the original input is also not in `UNSAT`
under this convention).
-/
noncomputable def unsatToSharpSAT (w : List BoolFormula) : List BoolFormula :=
  match w with
  | [φ] => enc.encode (φ, 0)
  | _ => enc.encode (BoolFormula.falseConst, 0)

/-- The constant `false` formula is unsatisfiable. -/
theorem BoolFormula.not_satisfiable_falseConst : ¬BoolFormula.falseConst.Satisfiable := by
  intro ⟨σ, hσ⟩
  simp [eval] at hσ

/-- The constant `false` formula has zero satisfying assignments. -/
theorem BoolFormula.countSat_falseConst : BoolFormula.falseConst.countSat = 0 :=
  countSat_eq_zero_of_not_satisfiable not_satisfiable_falseConst

/--
Correctness of the `unsatToSharpSAT` reduction: `w ∈ SATᶜ` iff
`unsatToSharpSAT w ∈ #SAT`. Concretely, for a single-formula input `[φ]`, this
says `φ` is unsatisfiable iff `countSat φ = 0`.
-/
theorem unsatToSharpSAT_correct :
    ∀ w : List BoolFormula,
      w ∈ SATLangᶜ ↔ unsatToSharpSAT enc w ∈ SharpSATLang enc := by
  intro w
  simp only [Set.mem_compl_iff, SATLang, Set.mem_setOf_eq,
             SharpSATLang, Set.mem_setOf_eq, unsatToSharpSAT]
  constructor
  · intro hw
    push Not at hw
    match w with
    | [φ] =>
      have hunsat : ¬φ.Satisfiable := hw φ rfl
      exact ⟨φ, 0, enc.decode_encode (φ, 0),
             (BoolFormula.countSat_eq_zero_of_not_satisfiable hunsat).symm⟩
    | [] =>
      exact ⟨BoolFormula.falseConst, 0, enc.decode_encode _,
             BoolFormula.countSat_falseConst.symm⟩
    | a :: b :: rest =>
      exact ⟨BoolFormula.falseConst, 0, enc.decode_encode _,
             BoolFormula.countSat_falseConst.symm⟩
  · intro ⟨φ', k, hdec, hk⟩
    push Not
    intro ψ hw_eq
    subst hw_eq
    simp only at hdec
    have hdec0 := enc.decode_encode (ψ, 0)
    rw [hdec0] at hdec
    have hinj := Option.some_injective _ hdec
    have hφ'_eq : φ' = ψ := ((Prod.ext_iff.mp hinj).1).symm
    have hk_eq : k = 0 := ((Prod.ext_iff.mp hinj).2).symm
    subst hφ'_eq; subst hk_eq
    exact BoolFormula.not_satisfiable_of_countSat_eq_zero (by omega)




end CoNPHardness

end NPCompleteness
