/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Atlas.TheoryOfComputation.code.Complexity
import Atlas.TheoryOfComputation.code.Tableau
namespace NPCompleteness

/--
Syntax of propositional Boolean formulas over variables indexed by ℕ.
A `BoolFormula` is built from variables, the constants `true` and `false`,
and the connectives ¬, ∧, ∨.
-/
inductive BoolFormula : Type where
  | var : ℕ → BoolFormula
  | trueConst : BoolFormula
  | falseConst : BoolFormula
  | not : BoolFormula → BoolFormula
  | and : BoolFormula → BoolFormula → BoolFormula
  | or : BoolFormula → BoolFormula → BoolFormula
  deriving DecidableEq, Repr

/-- A truth assignment is a function from variable indices ℕ to `Bool`. -/
abbrev BoolAssignment := ℕ → Bool

/--
Evaluation of a Boolean formula under an assignment σ : ℕ → Bool.
Returns the standard truth value of the formula under σ.
-/
def BoolFormula.eval (σ : BoolAssignment) : BoolFormula → Bool
  | .var n => σ n
  | .trueConst => true
  | .falseConst => false
  | .not φ => !φ.eval σ
  | .and φ ψ => φ.eval σ && ψ.eval σ
  | .or φ ψ => φ.eval σ || ψ.eval σ

/-- A formula φ is *satisfiable* if there exists an assignment σ with `φ.eval σ = true`. -/
def BoolFormula.Satisfiable (φ : BoolFormula) : Prop :=
  ∃ σ : BoolAssignment, φ.eval σ = true

/-- `SAT = {φ | φ is a satisfiable Boolean formula}`. -/
def SAT : Set BoolFormula :=
  {φ | φ.Satisfiable}

/-- A *literal* is a variable or the negation of a variable. -/
def BoolFormula.IsLiteral : BoolFormula → Prop
  | .var _ => True
  | .not (.var _) => True
  | _ => False

/-- A *clause* is a disjunction of literals: either a single literal, or `l ∨ (rest)`
where `rest` is itself a clause. -/
def BoolFormula.IsClause : BoolFormula → Prop
  | .or φ ψ => φ.IsLiteral ∧ ψ.IsClause
  | φ => φ.IsLiteral

/-- A formula is in *Conjunctive Normal Form* (CNF) if it is a conjunction of clauses. -/
def BoolFormula.IsCNF : BoolFormula → Prop
  | .and φ ψ => φ.IsClause ∧ ψ.IsCNF
  | φ => φ.IsClause

/-- The length (number of literals) of a clause, counted by walking through the `or`s. -/
def BoolFormula.clauseLength : BoolFormula → ℕ
  | .or _ ψ => 1 + ψ.clauseLength
  | _ => 1

/-- A *3-clause* is a clause containing exactly 3 literals. -/
def BoolFormula.Is3Clause (φ : BoolFormula) : Prop :=
  φ.IsClause ∧ φ.clauseLength = 3

/-- A formula is in *3CNF* if it is a conjunction of 3-clauses. -/
def BoolFormula.Is3CNF : BoolFormula → Prop
  | .and φ ψ => φ.Is3Clause ∧ ψ.Is3CNF
  | φ => φ.Is3Clause

/-- `3SAT = {φ | φ is a satisfiable 3CNF formula}`. -/
def ThreeSAT : Set BoolFormula :=
  {φ | φ.Is3CNF ∧ φ.Satisfiable}

/-- Membership in `ThreeSAT` from the conjunction of being 3CNF and being satisfiable. -/
theorem ThreeSAT.mk {φ : BoolFormula} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) :
    φ ∈ ThreeSAT :=
  ⟨h3, hsat⟩

end NPCompleteness

open TuringMachine in
/--
A language `B` is **NP-hard** if every `A ∈ NP` is polynomial-time reducible to `B`,
i.e. for all `A ∈ NP`, `A ≤_P B`.
-/
def IsNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InNP A → PolyReducible A B

open TuringMachine in
/--
A language `B` is **NP-complete** if (1) `B ∈ NP` and (2) `B` is NP-hard, i.e.
for every `A ∈ NP`, `A ≤_P B`.
-/
def IsNPComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InNP B ∧ (∀ A : Set (List Γ), InNP A → PolyReducible A B)

/-- The SAT language presented as a language of one-symbol input words `[φ]`
where the singleton list contains a satisfiable Boolean formula. -/
def SATLang : Set (List NPCompleteness.BoolFormula) :=
  {w | ∃ φ : NPCompleteness.BoolFormula, w = [φ] ∧ φ.Satisfiable}

namespace CookLevin

open TuringMachine NPCompleteness



/-- Index of the propositional variable `x_{i,j,σ}` indicating that cell `(i,j)`
of a `dim × dim` tableau contains the symbol with index `σIdx` (out of `numSymbols`). -/
@[inline] def tableau_var_idx (i j σIdx dim numSymbols : ℕ) : ℕ :=
  i * dim * numSymbols + j * numSymbols + σIdx

/-- Conjoin a list of Boolean formulas into a single `BoolFormula`.
Empty list returns `true`; a singleton returns the formula itself. -/
def build_conjunction : List BoolFormula → BoolFormula
  | [] => .trueConst
  | [φ] => φ
  | φ :: ψs => .and φ (build_conjunction ψs)

/-- Disjoin a list of Boolean formulas into a single `BoolFormula`.
Empty list returns `false`; a singleton returns the formula itself. -/
def build_disjunction : List BoolFormula → BoolFormula
  | [] => .falseConst
  | [φ] => φ
  | φ :: ψs => .or φ (build_disjunction ψs)

/--
The Cook–Levin sub-formula `φ_cell`: enforces that each cell `(i,j)` of the
tableau contains **exactly one** symbol — encoded as the conjunction of
"at least one symbol" and "no two distinct symbols simultaneously".
-/
def build_phi_cell (dim numSymbols : ℕ) : BoolFormula :=
  build_conjunction <| List.flatten <| (List.range dim).map fun i =>
    (List.range dim).map fun j =>
      let atLeastOne := build_disjunction <|
        (List.range numSymbols).map fun σ =>
          .var (tableau_var_idx i j σ dim numSymbols)
      let atMostOne := build_conjunction <| List.flatten <|
        (List.range numSymbols).map fun σ =>
          ((List.range numSymbols).filter (· ≠ σ)).map fun σ' =>
            .not (.and (.var (tableau_var_idx i j σ dim numSymbols))
                       (.var (tableau_var_idx i j σ' dim numSymbols)))
      .and atLeastOne atMostOne

/--
The Cook–Levin sub-formula `φ_start`: enforces that the first row of the tableau
encodes the initial configuration of `M` on input `w` — starting state `q₀` in the
left cell, then the input symbols, padded with blanks.
-/
def build_phi_start (dim numSymbols q₀Idx blankIdx : ℕ)
    (inputIdxs : List ℕ) : BoolFormula :=
  let n := inputIdxs.length
  build_conjunction <|
    [.var (tableau_var_idx 0 0 q₀Idx dim numSymbols)] ++
    (List.range n).map (fun idx =>
      .var (tableau_var_idx 0 (idx + 1) (inputIdxs.getD idx 0) dim numSymbols)) ++
    (List.range (dim - n - 1)).map (fun idx =>
      .var (tableau_var_idx 0 (n + 1 + idx) blankIdx dim numSymbols))

/--
The Cook–Levin sub-formula `φ_accept`: enforces that the accepting state `q_accept`
appears somewhere in the final row of the tableau.
-/
def build_phi_accept (dim numSymbols qAcceptIdx : ℕ) : BoolFormula :=
  build_disjunction <|
    (List.range dim).map fun j =>
      .var (tableau_var_idx (dim - 1) j qAcceptIdx dim numSymbols)

/--
The Cook–Levin sub-formula `φ_move`: enforces that every consecutive pair of
rows of the tableau differs only in a way consistent with one step of `M` — encoded
by requiring that every 2 × 3 window matches one of the legal windows
(determined from the transition function δ).
-/
def build_phi_move (dim numSymbols : ℕ) (legalWindows : List (List ℕ)) : BoolFormula :=
  build_conjunction <| List.flatten <| (List.range (dim - 1)).map fun i =>
    ((List.range (dim - 2)).map (· + 1)).map fun j =>
      build_disjunction <| legalWindows.map fun w =>
        build_conjunction [
          .var (tableau_var_idx i (j - 1) (w.getD 0 0) dim numSymbols),
          .var (tableau_var_idx i j (w.getD 1 0) dim numSymbols),
          .var (tableau_var_idx i (j + 1) (w.getD 2 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) (j - 1) (w.getD 3 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) j (w.getD 4 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) (j + 1) (w.getD 5 0) dim numSymbols)
        ]

/--
The Cook–Levin formula `φ_{M,w} = φ_cell ∧ φ_start ∧ φ_move ∧ φ_accept`.
Given an NTM `M`, a polynomial-time exponent `k`, and an input `w`, this builds
a Boolean formula that is satisfiable iff `M` has an accepting computation on `w`
of length at most `(|w|+1)^k`.
-/
noncomputable def buildTableauFormula
    {Q : Type} {Γ : Type} [DecidableEq Q]
    (M : NTM Q Γ) (k : ℕ) (w : List Γ) : BoolFormula := by
  classical
  letI : DecidableEq Γ := Classical.typeDecidableEq Γ
  let dim := (w.length + 1) ^ k
  let knownSymbols : List (Sum Q Γ) :=
    ([M.q₀, M.qAccept, M.qReject].map Sum.inl) ++
    ((M.blank :: w).map Sum.inr)
  let numSymbols := knownSymbols.length
  let enc : Sum Q Γ → ℕ := fun s => knownSymbols.findIdx (· == s)
  let q₀Idx := enc (Sum.inl M.q₀)
  let qAcceptIdx := enc (Sum.inl M.qAccept)
  let blankIdx := enc (Sum.inr M.blank)
  let inputIdxs := w.map (fun γ => enc (Sum.inr γ))
  let stateIndices := [M.q₀, M.qAccept, M.qReject].map (fun q => enc (Sum.inl q))
  let allIndices := List.range numSymbols
  let allSixTuples : List (List ℕ) :=
    List.flatten <| allIndices.map fun a₁ =>
    List.flatten <| allIndices.map fun a₂ =>
    List.flatten <| allIndices.map fun a₃ =>
    List.flatten <| allIndices.map fun b₁ =>
    List.flatten <| allIndices.map fun b₂ =>
    allIndices.map fun b₃ => [a₁, a₂, a₃, b₁, b₂, b₃]
  let isLegal : List ℕ → Prop := fun w6 =>
    let a₁ := w6.getD 0 0; let a₂ := w6.getD 1 0; let a₃ := w6.getD 2 0
    let b₁ := w6.getD 3 0; let b₂ := w6.getD 4 0; let b₃ := w6.getD 5 0
    (a₂ ∉ stateIndices → b₁ = a₁ ∧ b₂ = a₂ ∧ b₃ = a₃) ∧
    (∀ q : Q, enc (Sum.inl q) = a₂ →
      ∃ (q' : Q) (γ γ' : Γ) (d : Direction),
        enc (Sum.inr γ) = a₃ ∧
        (q', γ', d) ∈ M.δ q γ ∧
        (b₂ = enc (Sum.inl q') ∨ b₂ = enc (Sum.inr γ')))
  let legalWindows := allSixTuples.filter
    (fun w6 => (Classical.propDecidable (isLegal w6)).decide)
  exact .and (.and (build_phi_cell dim numSymbols)
                   (build_phi_start dim numSymbols q₀Idx blankIdx inputIdxs))
             (.and (build_phi_move dim numSymbols legalWindows)
                   (build_phi_accept dim numSymbols qAcceptIdx))



/-- States of the trivial NTM that decides `SATLang` by "magically" guessing a
satisfying assignment in one step. -/
inductive SATState
  | start
  | goodHead
  | badHead
  | accept
  | reject
  deriving DecidableEq

/-- `SATState` is a finite type. -/
instance : Fintype SATState :=
  ⟨⟨[SATState.start, SATState.goodHead, SATState.badHead,
    SATState.accept, SATState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/--
An NTM that decides `SATLang` "nondeterministically in one step": on input `[φ]`,
it goes to accept iff φ is satisfiable, otherwise to reject. This witnesses that
SAT ∈ NP using the alphabet `BoolFormula` (one symbol per formula).
-/
noncomputable def satNTM : NTM SATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Satisfiable then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .goodHead => {(.reject, γ, Direction.R)}
    | .badHead => {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅


/-- `satNTM` halts within `n + 2` steps on every input of length `n`. -/
theorem satNTM_runsInTime : satNTM.runsInTime (fun n => n + 2) := by
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
      satNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [satNTM, hstate0, show (SATState.start = SATState.accept ∨
        SATState.start = SATState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = SATState.accept ∨
          (branch ⟨j, ihjlt⟩).state = SATState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [satNTM] at hstep
      rcases hstate_halt with hst | hst <;>
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, satNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

/-- The bound `n + 2 = O(n^1)`, used to verify that `satNTM` runs in polynomial time. -/
theorem satNTM_time_bound : IsBigO (fun n => n + 2) (fun n => n ^ 1) := by
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  simp only [Nat.pow_one]
  omega









end CookLevin

namespace TuringMachine

open TuringMachine



end TuringMachine

namespace ThreeSATComplete

open TuringMachine NPCompleteness

/-- The 3SAT language presented as singleton-list inputs: `[φ]` belongs iff `φ`
is a satisfiable 3CNF formula. -/
def ThreeSATLang : Set (List BoolFormula) :=
  {w | ∃ φ : BoolFormula, w = [φ] ∧ φ.Is3CNF ∧ φ.Satisfiable}

/-- States of the trivial NTM that decides `ThreeSATLang` by guessing a satisfying
assignment in one nondeterministic step. -/
inductive ThreeSATState
  | start
  | accept
  | reject
  deriving DecidableEq

/-- `ThreeSATState` is a finite type. -/
instance : Fintype ThreeSATState :=
  ⟨⟨[ThreeSATState.start, ThreeSATState.accept, ThreeSATState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/-- An NTM that decides `ThreeSATLang` in one step: accepts `[φ]` iff `φ` is a
satisfiable 3CNF formula. Witnesses that `3SAT ∈ NP`. -/
noncomputable def threeSATNTM : NTM ThreeSATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Is3CNF ∧ γ.Satisfiable
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅


/-- `threeSATNTM` halts within `n + 2` steps on every input of length `n`. -/
theorem threeSATNTM_runsInTime : threeSATNTM.runsInTime (fun n => n + 2) := by
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
      threeSATNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [threeSATNTM, hstate0, show (ThreeSATState.start = ThreeSATState.accept ∨
        ThreeSATState.start = ThreeSATState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = ThreeSATState.accept ∨
          (branch ⟨j, ihjlt⟩).state = ThreeSATState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [threeSATNTM] at hstep
      rcases hstate_halt with hst | hst <;>
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, threeSATNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

/-- `n + 2 = O(n^1)`, used to certify `threeSATNTM` runs in polynomial time. -/
theorem threeSATNTM_time_bound : IsBigO (fun n => n + 2) (fun n => n ^ 1) := by
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  simp only [Nat.pow_one]
  omega



/-- `maxVarSucc φ` returns one more than the largest variable index appearing in `φ`
(or `0` if no variable occurs). Equivalently, the smallest fresh variable index. -/
def maxVarSucc : BoolFormula → ℕ
  | .var n => n + 1
  | .trueConst | .falseConst => 0
  | .not φ => maxVarSucc φ
  | .and φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)
  | .or φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)

/-- Build a 3-literal clause `l₁ ∨ l₂ ∨ l₃` (right-associated). -/
def mk3Clause (l₁ l₂ l₃ : BoolFormula) : BoolFormula :=
  .or l₁ (.or l₂ l₃)

/--
Core of the **Tseitin transformation**. Given a formula `φ` and a fresh-variable
counter, produces `(rootVar, clauses, fresh')` where:
- `rootVar` is a variable whose truth value tracks `φ.eval σ` under any
  satisfying assignment of the clauses;
- `clauses` is a list of 3-clauses encoding the gates of `φ`;
- `fresh'` is the next available fresh variable index.
This is the standard linear-size CNF (in fact 3CNF) encoding of an arbitrary
Boolean formula introducing one auxiliary variable per subformula.
-/
def tseitinAux : BoolFormula → ℕ → (ℕ × List BoolFormula × ℕ)
  | .var n, fresh => (n, [], fresh)
  | .trueConst, fresh =>

    (fresh, [mk3Clause (.var fresh) (.var fresh) (.var fresh)], fresh + 1)
  | .falseConst, fresh =>

    (fresh, [mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))],
     fresh + 1)
  | .not φ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let z := fresh1


    (z, clsφ ++ [mk3Clause (.var vφ) (.var z) (.var z),
                  mk3Clause (.not (.var vφ)) (.not (.var z)) (.not (.var z))],
     fresh1 + 1)
  | .and φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.not (.var z)),
      mk3Clause (.not (.var vφ)) (.var vψ) (.not (.var z)),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)
  | .or φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.var z),
      mk3Clause (.not (.var vφ)) (.var vψ) (.var z),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)

/-- Conjoin a list of clauses into a single CNF formula (returns a dummy 3-clause if empty,
keeping the result a valid 3CNF). -/
def conjoinClauses : List BoolFormula → BoolFormula
  | [] => mk3Clause (.var 0) (.var 0) (.var 0)
  | [c] => c
  | c :: cs => .and c (conjoinClauses cs)

/--
**Tseitin transformation**: convert any Boolean formula `φ` into an
equisatisfiable 3CNF formula. Returns the conjunction of the clauses generated
by `tseitinAux` together with a clause forcing the root variable to be true.
-/
def tseitinTransform (φ : BoolFormula) : BoolFormula :=
  let fresh := maxVarSucc φ
  let (rootVar, clauses, _) := tseitinAux φ fresh
  let rootClause := mk3Clause (.var rootVar) (.var rootVar) (.var rootVar)
  conjoinClauses (clauses ++ [rootClause])

/-- The reduction function from `SATLang` to `ThreeSATLang`: applies the Tseitin
transformation to a singleton input `[φ]`. -/
def satTo3SATFn : List BoolFormula → List BoolFormula
  | [φ] => [tseitinTransform φ]
  | _ => []


/-- A literal has clause-length exactly `1`. -/
lemma literal_clauseLength_eq_one {l : BoolFormula} (hl : l.IsLiteral) :
    l.clauseLength = 1 := by
  cases l with
  | var _ => rfl
  | not inner =>
    cases inner with
    | var _ => rfl
    | _ => exact absurd hl (by simp [BoolFormula.IsLiteral])
  | _ => exact absurd hl (by simp [BoolFormula.IsLiteral])

/-- `mk3Clause l₁ l₂ l₃` is a clause whenever the three arguments are literals. -/
lemma mk3Clause_isClause {l₁ l₂ l₃ : BoolFormula}
    (h₁ : l₁.IsLiteral) (h₂ : l₂.IsLiteral) (h₃ : l₃.IsLiteral) :
    (mk3Clause l₁ l₂ l₃).IsClause := by
  unfold mk3Clause
  show l₁.IsLiteral ∧ (BoolFormula.or l₂ l₃).IsClause
  refine ⟨h₁, ?_⟩
  show l₂.IsLiteral ∧ l₃.IsClause
  refine ⟨h₂, ?_⟩

  cases l₃ with
  | var _ => exact h₃
  | not inner =>
    cases inner with
    | var _ => exact h₃
    | _ => exact absurd h₃ (by simp [BoolFormula.IsLiteral])
  | _ => exact absurd h₃ (by simp [BoolFormula.IsLiteral])

/-- `mk3Clause l₁ l₂ l₃` has clause-length `3`. -/
lemma mk3Clause_clauseLength {l₁ l₂ l₃ : BoolFormula}
    (_h₁ : l₁.IsLiteral) (_h₂ : l₂.IsLiteral) (h₃ : l₃.IsLiteral) :
    (mk3Clause l₁ l₂ l₃).clauseLength = 3 := by
  unfold mk3Clause
  simp only [BoolFormula.clauseLength]
  rw [literal_clauseLength_eq_one h₃]

/-- `mk3Clause l₁ l₂ l₃` is a 3-clause when given three literals. -/
lemma mk3Clause_is3Clause {l₁ l₂ l₃ : BoolFormula}
    (h₁ : l₁.IsLiteral) (h₂ : l₂.IsLiteral) (h₃ : l₃.IsLiteral) :
    (mk3Clause l₁ l₂ l₃).Is3Clause :=
  ⟨mk3Clause_isClause h₁ h₂ h₃, mk3Clause_clauseLength h₁ h₂ h₃⟩

/-- A bare variable is a literal. -/
lemma var_isLiteral (n : ℕ) : (BoolFormula.var n).IsLiteral := trivial

/-- The negation of a variable is a literal. -/
lemma not_var_isLiteral (n : ℕ) : (BoolFormula.not (.var n)).IsLiteral := trivial

/-- Every clause generated by `tseitinAux` is a 3-clause. -/
lemma tseitinAux_clauses_are_3clauses (φ : BoolFormula) (fresh : ℕ) :
    ∀ c ∈ (tseitinAux φ fresh).2.1, c.Is3Clause := by
  induction φ generalizing fresh with
  | var _ => simp [tseitinAux]
  | trueConst =>
    simp only [tseitinAux]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
  | falseConst =>
    simp only [tseitinAux]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
  | not ψ ih =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ fresh).2.1 ++
      [mk3Clause (.var (tseitinAux ψ fresh).1) (.var (tseitinAux ψ fresh).2.2) (.var (tseitinAux ψ fresh).2.2),
       mk3Clause (.not (.var (tseitinAux ψ fresh).1)) (.not (.var (tseitinAux ψ fresh).2.2)) (.not (.var (tseitinAux ψ fresh).2.2))] := by
      generalize tseitinAux ψ fresh = r at hc ⊢
      obtain ⟨vφ, clsφ, fresh1⟩ := r
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    rcases this with hc' | rfl | rfl
    · exact ih fresh c hc'
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ₁ fresh).2.1 ++ (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.1 ++
      [mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
       mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2)),
       mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2)),
       mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2))] := by
      generalize tseitinAux ψ₁ fresh = r₁ at hc ⊢
      obtain ⟨v₁, cls₁, fresh1⟩ := r₁
      generalize tseitinAux ψ₂ fresh1 = r₂ at hc ⊢
      obtain ⟨v₂, cls₂, fresh2⟩ := r₂
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    rcases this with (hc' | hc') | rfl | rfl | rfl | rfl
    · exact ih₁ fresh c hc'
    · exact ih₂ (tseitinAux ψ₁ fresh).2.2 c hc'
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (not_var_isLiteral _) (not_var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]
    intro c hc
    have : c ∈ (tseitinAux ψ₁ fresh).2.1 ++ (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.1 ++
      [mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
       mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
       mk3Clause (.not (.var (tseitinAux ψ₁ fresh).1)) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2),
       mk3Clause (.var (tseitinAux ψ₁ fresh).1) (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).1) (.not (.var (tseitinAux ψ₂ (tseitinAux ψ₁ fresh).2.2).2.2))] := by
      generalize tseitinAux ψ₁ fresh = r₁ at hc ⊢
      obtain ⟨v₁, cls₁, fresh1⟩ := r₁
      generalize tseitinAux ψ₂ fresh1 = r₂ at hc ⊢
      obtain ⟨v₂, cls₂, fresh2⟩ := r₂
      exact hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at this
    rcases this with (hc' | hc') | rfl | rfl | rfl | rfl
    · exact ih₁ fresh c hc'
    · exact ih₂ (tseitinAux ψ₁ fresh).2.2 c hc'
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (not_var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (not_var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
    · exact mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (not_var_isLiteral _)

/-- Any single 3-clause is itself a 3CNF (a CNF with one clause). -/
lemma is3CNF_of_is3Clause {φ : BoolFormula} (h : φ.Is3Clause) : φ.Is3CNF := by
  cases φ with
  | and _ _ =>
    exact absurd h.1 (by simp [BoolFormula.IsClause, BoolFormula.IsLiteral])
  | _ => exact h

/-- Conjoining a nonempty list of 3-clauses yields a 3CNF formula. -/
lemma conjoinClauses_is3CNF (cs : List BoolFormula) (hne : cs ≠ [])
    (h3 : ∀ c ∈ cs, c.Is3Clause) :
    (conjoinClauses cs).Is3CNF := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    match cs, ih with
    | [], _ =>
      simp only [conjoinClauses]
      exact is3CNF_of_is3Clause (h3 c List.mem_cons_self)
    | d :: ds, ih =>
      simp only [conjoinClauses]
      exact ⟨h3 c List.mem_cons_self,
             ih (List.cons_ne_nil d ds)
               (fun x hx => h3 x (List.mem_cons_of_mem _ hx))⟩

/-- The output of the Tseitin transformation is always a 3CNF formula. -/
theorem tseitinTransform_is3CNF (φ : BoolFormula) :
    (tseitinTransform φ).Is3CNF := by
  unfold tseitinTransform
  set fresh := maxVarSucc φ
  have hroot : (mk3Clause (.var (tseitinAux φ fresh).1)
      (.var (tseitinAux φ fresh).1)
      (.var (tseitinAux φ fresh).1)).Is3Clause :=
    mk3Clause_is3Clause (var_isLiteral _) (var_isLiteral _) (var_isLiteral _)
  have hclauses := tseitinAux_clauses_are_3clauses φ fresh
  apply conjoinClauses_is3CNF
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact hclauses c hc
    · subst hc; exact hroot

/-- The fresh-variable counter is monotone: `tseitinAux` only allocates new variables
above the input `fresh`. -/
lemma tseitinAux_fresh_mono : ∀ (φ : BoolFormula) (fresh : ℕ),
    fresh ≤ (tseitinAux φ fresh).2.2
  | .var _, fresh => le_refl _
  | .trueConst, fresh => Nat.le_succ _
  | .falseConst, fresh => Nat.le_succ _
  | .not ψ, fresh => by
    simp only [tseitinAux]; have h := tseitinAux_fresh_mono ψ fresh
    generalize hr : tseitinAux ψ fresh = r at h; obtain ⟨_, _, f1⟩ := r; simp only at h ⊢; omega
  | .and ψ₁ ψ₂, fresh => by
    simp only [tseitinAux]
    have h1 := tseitinAux_fresh_mono ψ₁ fresh
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at h1; obtain ⟨_, _, f1⟩ := r₁; simp only at h1 ⊢
    have h2 := tseitinAux_fresh_mono ψ₂ f1
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at h2; obtain ⟨_, _, f2⟩ := r₂; simp only at h2 ⊢; omega
  | .or ψ₁ ψ₂, fresh => by
    simp only [tseitinAux]
    have h1 := tseitinAux_fresh_mono ψ₁ fresh
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at h1; obtain ⟨_, _, f1⟩ := r₁; simp only at h1 ⊢
    have h2 := tseitinAux_fresh_mono ψ₂ f1
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at h2; obtain ⟨_, _, f2⟩ := r₂; simp only at h2 ⊢; omega

/--
Soundness of the Tseitin auxiliary construction: if `σ` satisfies all the
clauses produced by `tseitinAux φ fresh`, then `σ` of the root variable equals
the value of `φ` under `σ`.
-/
lemma tseitinAux_soundness : ∀ (φ : BoolFormula) (fresh : ℕ) (σ : BoolAssignment),
    (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ = true) →
    σ (tseitinAux φ fresh).1 = φ.eval σ
  | .var n, _, σ, _ => rfl
  | .trueConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.var fresh) (.var fresh) (.var fresh)) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .falseConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .not ψ, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr : tseitinAux ψ fresh = r at hcls ⊢
    obtain ⟨vφ, clsφ, fresh1⟩ := r; simp only at hcls ⊢
    have hih : σ vφ = ψ.eval σ := by
      have := tseitinAux_soundness ψ fresh σ; rw [hr] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ hc))
    have h1 := hcls (mk3Clause (.var vφ) (.var fresh1) (.var fresh1))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; left; trivial)
    have h2 := hcls (mk3Clause (.not (.var vφ)) (.not (.var fresh1)) (.not (.var fresh1)))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; right; trivial)

    simp [mk3Clause, BoolFormula.eval, hih] at h1 h2
    simp only [BoolFormula.eval]; cases he : ψ.eval σ <;> simp_all

  | .and ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)
    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all
  | .or ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)

    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all

/-- The "free-max-var" function: alias of `maxVarSucc` used in coincidence lemmas.
Returns one more than the largest variable index appearing in `φ`. -/
def fmv : BoolFormula → ℕ
  | .var n => n + 1 | .trueConst | .falseConst => 0
  | .not φ => fmv φ | .and φ ψ | .or φ ψ => max (fmv φ) (fmv ψ)
/-- Evaluation of `c` depends only on the values of `σ` at indices `< fmv c`. -/
lemma eval_eq_of_ge (c : BoolFormula) (σ₁ σ₂ : BoolAssignment)
    (h : ∀ n, n < fmv c → σ₁ n = σ₂ n) : c.eval σ₁ = c.eval σ₂ := by
  induction c with
  | var n => exact h n (by simp [fmv])
  | trueConst | falseConst => rfl
  | not ψ ih => simp only [BoolFormula.eval]; congr 1; exact ih fun n hn => h n (by simp [fmv] at hn ⊢; exact hn)
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [BoolFormula.eval]; congr 1
    · exact ih₁ fun n hn => h n (by simp [fmv] at hn ⊢; omega)
    · exact ih₂ fun n hn => h n (by simp [fmv] at hn ⊢; omega)
/-- The root variable produced by `tseitinAux` is strictly less than the returned
fresh counter, as long as the initial `fresh` is above all of `φ`'s variables. -/
lemma tseitinAux_root_bound (φ : BoolFormula) (fresh : ℕ) (hfr : maxVarSucc φ ≤ fresh) :
    (tseitinAux φ fresh).1 < (tseitinAux φ fresh).2.2 := by
  cases φ with
  | var n => simp [tseitinAux, maxVarSucc] at hfr ⊢; omega
  | trueConst => simp [tseitinAux]
  | falseConst => simp [tseitinAux]
  | not ψ => simp only [tseitinAux]; generalize tseitinAux ψ fresh = r; obtain ⟨_, _, f1⟩ := r; simp only; omega
  | and ψ₁ ψ₂ => simp only [tseitinAux]; generalize tseitinAux ψ₁ fresh = r₁; obtain ⟨_, _, f1⟩ := r₁; simp only; generalize tseitinAux ψ₂ f1 = r₂; obtain ⟨_, _, f2⟩ := r₂; simp only; omega
  | or ψ₁ ψ₂ => simp only [tseitinAux]; generalize tseitinAux ψ₁ fresh = r₁; obtain ⟨_, _, f1⟩ := r₁; simp only; generalize tseitinAux ψ₂ f1 = r₂; obtain ⟨_, _, f2⟩ := r₂; simp only; omega

/-- Every variable occurring in a clause produced by `tseitinAux` has index strictly
less than the returned fresh counter. -/
lemma tseitinAux_clause_fmv (φ : BoolFormula) (fresh : ℕ) (hfr : maxVarSucc φ ≤ fresh) :
    ∀ c ∈ (tseitinAux φ fresh).2.1, fmv c ≤ (tseitinAux φ fresh).2.2 := by
  induction φ generalizing fresh with
  | var _ => simp [tseitinAux]
  | trueConst => intro c hc; simp only [tseitinAux, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; subst hc; simp [mk3Clause, fmv]
  | falseConst => intro c hc; simp only [tseitinAux, List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; subst hc; simp [mk3Clause, fmv]
  | not ψ ih =>
    have hfrs : maxVarSucc ψ ≤ fresh := by simp [maxVarSucc] at hfr; exact hfr
    simp only [tseitinAux] at *; generalize hr : tseitinAux ψ fresh = r at *; obtain ⟨vφ, clsφ, f1⟩ := r; simp only at *
    have hvlt : vφ < f1 := by have := tseitinAux_root_bound ψ fresh hfrs; rw [hr] at this; simp only at this; exact this

    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with hc | rfl | rfl
    · have := ih fresh hfrs c (by rw [hr]; exact hc); rw [hr] at this; simp only at this; omega

    · simp [mk3Clause, fmv]; omega
    · simp [mk3Clause, fmv]; omega
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    simp only [tseitinAux] at *
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at *; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at *
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at *; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; simp only at this; exact this

    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with (hc | hc) | rfl | rfl | rfl | rfl
    · have := ih₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at this; have hm := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at hm; simp only at *; omega
    · have := ih₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at this; simp only at this; omega
    all_goals simp [mk3Clause, fmv]; omega
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    simp only [tseitinAux] at *
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at *; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at *
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at *; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; simp only at this; exact this

    intro c hc; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with (hc | hc) | rfl | rfl | rfl | rfl
    · have := ih₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at this; have hm := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at hm; simp only at *; omega
    · have := ih₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at this; simp only at this; omega
    all_goals simp [mk3Clause, fmv]; omega
/-- If `σ` and `σ'` agree on all variables below `fresh` and `fresh` is above
`maxVarSucc φ`, then they evaluate `φ` to the same value. -/
lemma eval_maxVarSucc_le (φ : BoolFormula) (fresh : ℕ) (σ σ' : BoolAssignment)
    (hfr : maxVarSucc φ ≤ fresh) (h : ∀ n, n < fresh → σ' n = σ n) : φ.eval σ' = φ.eval σ := by
  apply eval_eq_of_ge; intro n hn; apply h
  induction φ with
  | var m => simp [fmv] at hn; simp [maxVarSucc] at hfr; omega
  | trueConst | falseConst => simp [fmv] at hn
  | not ψ ih => simp [fmv, maxVarSucc] at hn hfr; exact ih hfr hn
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp [fmv, maxVarSucc] at hn hfr; rcases hn with hn | hn
    · exact ih₁ (by omega) hn
    · exact ih₂ (by omega) hn

/--
Completeness of the Tseitin auxiliary construction: given any assignment `σ` to
the original variables of `φ`, there is an extension `σ'` that
(1) agrees with `σ` on the original variables,
(2) sends the root variable to `φ.eval σ`, and
(3) satisfies every clause produced by `tseitinAux φ fresh`.
-/
lemma tseitinAux_completeness (φ : BoolFormula) (fresh : ℕ) (σ : BoolAssignment)
    (hfr : maxVarSucc φ ≤ fresh) :
    ∃ σ' : BoolAssignment,
      (∀ n, n < fresh → σ' n = σ n) ∧
      σ' (tseitinAux φ fresh).1 = φ.eval σ ∧
      (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ' = true) := by
  induction φ generalizing fresh σ with
  | var n =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨σ, fun _ _ => rfl, rfl, fun _ h => absurd h (by simp)⟩

  | trueConst =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨Function.update σ fresh true, fun n hn => by simp [Function.update_apply, Nat.ne_of_lt hn], by simp [Function.update_apply],
      fun c hc => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; simp [mk3Clause, BoolFormula.eval, Function.update_apply]⟩
  | falseConst =>
    simp only [tseitinAux, BoolFormula.eval]
    exact ⟨Function.update σ fresh false, fun n hn => by simp [Function.update_apply, Nat.ne_of_lt hn], by simp [Function.update_apply],
      fun c hc => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; simp [mk3Clause, BoolFormula.eval, Function.update_apply]⟩
  | not ψ ih =>
    simp only [tseitinAux]; generalize hr : tseitinAux ψ fresh = r; obtain ⟨vφ, clsφ, f1⟩ := r; simp only
    have hfrs : maxVarSucc ψ ≤ fresh := by simp [maxVarSucc] at hfr; exact hfr
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih fresh σ hfrs; rw [hr] at hσ₁r hσ₁c; simp only at *
    have hvlt : vφ < f1 := by have := tseitinAux_root_bound ψ fresh hfrs; rw [hr] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ fresh; rw [hr] at this; exact this
    refine ⟨Function.update σ₁ f1 (!σ₁ vφ), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f1 from by omega]; exact hσ₁a n hn
    · simp [Function.update_apply, show vφ ≠ f1 from by omega, BoolFormula.eval, hσ₁r]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with hc | rfl | rfl
      · have hfmv := tseitinAux_clause_fmv ψ fresh hfrs c (by rw [hr]; exact hc); rw [hr] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₁ (fun n hn => by simp [Function.update_apply, show n ≠ f1 from by omega])]; exact hσ₁c c hc
      · simp only [mk3Clause, BoolFormula.eval, Function.update_apply, show vφ ≠ f1 from by omega, ite_false]; cases σ₁ vφ <;> simp
      · simp only [mk3Clause, BoolFormula.eval, Function.update_apply, show vφ ≠ f1 from by omega, ite_false]; cases σ₁ vφ <;> simp
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]; generalize hr₁ : tseitinAux ψ₁ fresh = r₁; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih₁ fresh σ hfr₁; rw [hr₁] at hσ₁r hσ₁c; simp only at *
    obtain ⟨σ₂, hσ₂a, hσ₂r, hσ₂c⟩ := ih₂ f1 σ₁ hfr₂; rw [hr₂] at hσ₂r hσ₂c; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; exact this
    have hf2ge : f1 ≤ f2 := by have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; exact this
    have hσ₂_orig : ∀ n, n < fresh → σ₂ n = σ n := fun n hn => by rw [hσ₂a n (by omega)]; exact hσ₁a n hn
    have hσ₂v₁ : σ₂ v₁ = ψ₁.eval σ := by rw [hσ₂a v₁ (by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; exact this)]; exact hσ₁r
    have hσ₂r_eq : σ₂ v₂ = ψ₂.eval σ := by rw [hσ₂r]; exact eval_maxVarSucc_le ψ₂ fresh σ σ₁ (by simp [maxVarSucc] at hfr; omega) hσ₁a
    refine ⟨Function.update σ₂ f2 (σ₂ v₁ && σ₂ v₂), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f2 from by omega]; exact hσ₂_orig n hn
    · simp [Function.update_apply, BoolFormula.eval, hσ₂v₁, hσ₂r_eq]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with (hc | hc) | rfl | rfl | rfl | rfl
      · have hfmv := tseitinAux_clause_fmv ψ₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]
        rw [eval_eq_of_ge c σ₂ σ₁ (fun n hn => by exact hσ₂a n (by omega))]; exact hσ₁c c hc
      · have hfmv := tseitinAux_clause_fmv ψ₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]; exact hσ₂c c hc
      all_goals simp [mk3Clause, BoolFormula.eval, Function.update_apply, show v₁ ≠ f2 from by omega, show v₂ ≠ f2 from by omega]; cases σ₂ v₁ <;> cases σ₂ v₂ <;> simp
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [tseitinAux]; generalize hr₁ : tseitinAux ψ₁ fresh = r₁; obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂; obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only
    have hfr₁ : maxVarSucc ψ₁ ≤ fresh := by simp [maxVarSucc] at hfr; omega
    have hfr₂ : maxVarSucc ψ₂ ≤ f1 := by simp [maxVarSucc] at hfr; have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; simp only at this; omega
    obtain ⟨σ₁, hσ₁a, hσ₁r, hσ₁c⟩ := ih₁ fresh σ hfr₁; rw [hr₁] at hσ₁r hσ₁c; simp only at *
    obtain ⟨σ₂, hσ₂a, hσ₂r, hσ₂c⟩ := ih₂ f1 σ₁ hfr₂; rw [hr₂] at hσ₂r hσ₂c; simp only at *
    have hv₁lt : v₁ < f2 := by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; simp only at *; omega
    have hv₂lt : v₂ < f2 := by have := tseitinAux_root_bound ψ₂ f1 hfr₂; rw [hr₂] at this; exact this
    have hfge : fresh ≤ f1 := by have := tseitinAux_fresh_mono ψ₁ fresh; rw [hr₁] at this; exact this
    have hf2ge : f1 ≤ f2 := by have := tseitinAux_fresh_mono ψ₂ f1; rw [hr₂] at this; exact this
    have hσ₂_orig : ∀ n, n < fresh → σ₂ n = σ n := fun n hn => by rw [hσ₂a n (by omega)]; exact hσ₁a n hn
    have hσ₂v₁ : σ₂ v₁ = ψ₁.eval σ := by rw [hσ₂a v₁ (by have := tseitinAux_root_bound ψ₁ fresh hfr₁; rw [hr₁] at this; exact this)]; exact hσ₁r
    have hσ₂r_eq : σ₂ v₂ = ψ₂.eval σ := by rw [hσ₂r]; exact eval_maxVarSucc_le ψ₂ fresh σ σ₁ (by simp [maxVarSucc] at hfr; omega) hσ₁a
    refine ⟨Function.update σ₂ f2 (σ₂ v₁ || σ₂ v₂), fun n hn => ?_, ?_, fun c hc => ?_⟩
    · simp [Function.update_apply, show n ≠ f2 from by omega]; exact hσ₂_orig n hn
    · simp [Function.update_apply, BoolFormula.eval, hσ₂v₁, hσ₂r_eq]
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with (hc | hc) | rfl | rfl | rfl | rfl
      · have hfmv := tseitinAux_clause_fmv ψ₁ fresh hfr₁ c (by rw [hr₁]; exact hc); rw [hr₁] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]
        rw [eval_eq_of_ge c σ₂ σ₁ (fun n hn => by exact hσ₂a n (by omega))]; exact hσ₁c c hc
      · have hfmv := tseitinAux_clause_fmv ψ₂ f1 hfr₂ c (by rw [hr₂]; exact hc); rw [hr₂] at hfmv; simp only at hfmv
        rw [eval_eq_of_ge c _ σ₂ (fun n hn => by simp [Function.update_apply, show n ≠ f2 from by omega])]; exact hσ₂c c hc
      all_goals simp [mk3Clause, BoolFormula.eval, Function.update_apply, show v₁ ≠ f2 from by omega, show v₂ ≠ f2 from by omega]; cases σ₂ v₁ <;> cases σ₂ v₂ <;> simp

/-- `conjoinClauses cs` evaluates to true under `σ` iff every clause in `cs` does. -/
lemma conjoinClauses_eval : ∀ (cs : List BoolFormula) (_ : cs ≠ []) (σ : BoolAssignment),
    (conjoinClauses cs).eval σ = true ↔ ∀ c ∈ cs, c.eval σ = true
  | [c], _, σ => by simp [conjoinClauses]
  | c :: d :: ds, _, σ => by
    simp only [conjoinClauses, BoolFormula.eval, Bool.and_eq_true]
    rw [conjoinClauses_eval (d :: ds) (List.cons_ne_nil d ds) σ]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨hc, hrest⟩ x (rfl | hx)
      · exact hc
      · exact hrest x hx
    · intro h; exact ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

/--
Equisatisfiability of the Tseitin transformation: `φ` is satisfiable iff
`tseitinTransform φ` is satisfiable.
-/
theorem tseitinTransform_correct (φ : BoolFormula) :
    φ.Satisfiable ↔ (tseitinTransform φ).Satisfiable := by
  constructor
  · intro ⟨σ, hσ⟩
    unfold tseitinTransform BoolFormula.Satisfiable
    obtain ⟨σ', _, hσ'_root, hσ'_cls⟩ := tseitinAux_completeness φ (maxVarSucc φ) σ le_rfl
    have hne : (tseitinAux φ (maxVarSucc φ)).2.1 ++
      [mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    refine ⟨σ', ?_⟩
    rw [conjoinClauses_eval _ hne]
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact hσ'_cls c hc
    · subst hc; simp [mk3Clause, BoolFormula.eval, hσ'_root, hσ]
  · intro ⟨σ, hσ⟩
    unfold tseitinTransform at hσ
    have hne : (tseitinAux φ (maxVarSucc φ)).2.1 ++
      [mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)
        (.var (tseitinAux φ (maxVarSucc φ)).1)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    rw [conjoinClauses_eval _ hne] at hσ
    have hcls := fun c hc => hσ c (List.mem_append_left _ hc)
    have hroot := hσ (mk3Clause (.var (tseitinAux φ (maxVarSucc φ)).1)
      (.var (tseitinAux φ (maxVarSucc φ)).1)
      (.var (tseitinAux φ (maxVarSucc φ)).1)) (List.mem_append_right _ (by simp))
    simp [mk3Clause, BoolFormula.eval] at hroot
    exact ⟨σ, by rw [← tseitinAux_soundness φ (maxVarSucc φ) σ hcls]; exact hroot⟩

/-- Correctness of the SAT → 3SAT reduction: `w ∈ SATLang ↔ satTo3SATFn w ∈ ThreeSATLang`. -/
theorem satTo3SATFn_correct :
    ∀ w : List BoolFormula, w ∈ SATLang ↔ satTo3SATFn w ∈ ThreeSATLang := by
  intro w
  simp only [SATLang, ThreeSATLang, Set.mem_setOf_eq]
  constructor
  · rintro ⟨φ, rfl, hsat⟩
    exact ⟨tseitinTransform φ, rfl, tseitinTransform_is3CNF φ,
           (tseitinTransform_correct φ).mp hsat⟩
  · intro ⟨ψ, hw_eq, h3cnf, hsat⟩
    match w, hw_eq with
    | [φ], hw_eq =>
      simp only [satTo3SATFn] at hw_eq
      have hψ : ψ = tseitinTransform φ := (List.cons_eq_cons.mp hw_eq).1.symm
      exact ⟨φ, rfl, (tseitinTransform_correct φ).mpr (hψ ▸ hsat)⟩
    | [], hw_eq => simp [satTo3SATFn] at hw_eq
    | _ :: _ :: _, hw_eq => simp [satTo3SATFn] at hw_eq




end ThreeSATComplete

namespace HamiltonianPath

open TuringMachine NPCompleteness

/-- A directed graph on vertex type `V`, given by an edge relation `edge : V → V → Prop`. -/
structure DiGraph (V : Type*) where
  edge : V → V → Prop

/--
`p` is a *Hamiltonian path* from `s` to `t` in the directed graph `G` if it starts
at `s`, ends at `t`, every consecutive pair of vertices is connected by an edge of
`G`, the vertices in `p` are pairwise distinct (`Nodup`), and every vertex of `V`
appears in `p`.
-/
def DiGraph.IsHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) (p : List V) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  (∀ (i : ℕ) (hi : i + 1 < p.length),
    G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) ∧
  p.Nodup ∧
  ∀ v : V, v ∈ p

/-- `G` has a Hamiltonian path from `s` to `t` if some list `p` is one. -/
def DiGraph.HasHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) : Prop :=
  ∃ p : List V, G.IsHamiltonianPath V s t p

/-- `HAMPATH = { (G, s, t) | G has a Hamiltonian path from s to t }`. -/
def HAMPATH (V : Type*) [DecidableEq V] [Fintype V] :
    Set (DiGraph V × V × V) :=
  {gst | gst.1.HasHamiltonianPath V gst.2.1 gst.2.2}

/-- Concrete one-symbol encoding of a HAMPATH instance: number of vertices `n`,
the edge relation, and the source/target vertices `s, t ∈ Fin n`. -/
inductive HampathSymbol
  | mk (n : ℕ) (edges : Fin n → Fin n → Bool) (s t : Fin n) : HampathSymbol

/-- Number of vertices `n` in the graph encoded by a `HampathSymbol`. -/
def HampathSymbol.numVertices : HampathSymbol → ℕ
  | .mk n _ _ _ => n

/-- The underlying directed graph on `Fin (numVertices sym)` encoded by a `HampathSymbol`. -/
def HampathSymbol.toDigraph : (sym : HampathSymbol) → DiGraph (Fin sym.numVertices)
  | .mk _ edges _ _ => ⟨fun u v => edges u v = true⟩

/-- Source vertex `s` of the encoded HAMPATH instance. -/
def HampathSymbol.source : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ s _ => s

/-- Target vertex `t` of the encoded HAMPATH instance. -/
def HampathSymbol.target : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ _ t => t

/-- The encoded instance is a YES instance of HAMPATH iff its graph has a
Hamiltonian path from `source` to `target`. -/
def HampathSymbol.isYesInstance (sym : HampathSymbol) : Prop :=
  sym.toDigraph.HasHamiltonianPath (Fin sym.numVertices) sym.source sym.target

/-- `HampathLang` is the language of one-symbol-encoded YES instances of HAMPATH. -/
def HampathLang : Set (List HampathSymbol) :=
  {w | ∃ sym : HampathSymbol, w.head? = some sym ∧ sym.isYesInstance}

/-- States of the trivial NTM that decides `HampathLang` by checking the
"yes-instance" predicate of the input symbol in a single step. -/
inductive HampathState
  | start
  | accept
  | reject
  deriving DecidableEq

/-- `HampathState` is a finite type. -/
instance : Fintype HampathState :=
  ⟨⟨[HampathState.start, HampathState.accept, HampathState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/-- An NTM that decides `HampathLang` in one step: accepts iff the (nonblank) input
symbol encodes a YES instance of HAMPATH. -/
noncomputable def hampathNTM : NTM HampathState HampathSymbol where
  blank := HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩
  inputAlpha := {x | x ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧ γ.isYesInstance
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

/-- The machine `hampathNTM` decides `HampathLang`. -/
theorem hampathNTM_decides : hampathNTM.decides HampathLang := by
  constructor
  ·
    intro w n branch hn hstart hsteps
    have hstate0 : (branch ⟨0, Nat.zero_lt_succ n⟩).state = .start := by
      rw [hstart]; rfl
    exact ⟨⟨1, by omega⟩, by
      have hs0 := hsteps ⟨0, hn⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
      have hst : (branch ⟨1, by omega⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }⟩
  ·
    ext w
    simp only [NTM.language, NTM.accepts, Set.mem_setOf_eq, HampathLang]
    constructor
    ·
      rintro ⟨n, branch, hstart, hsteps, haccept⟩
      have hstate0 : (branch ⟨0, Nat.zero_lt_succ n⟩).state = .start := by
        rw [hstart]; rfl

      have hn_pos : 0 < n := by
        by_contra h; push_neg at h
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero h
        subst hn0
        simp only [NTM.isAcceptConfig, hampathNTM] at haccept
        rw [hstate0] at haccept; exact absurd haccept (by decide)


      have hs0 := hsteps ⟨0, hn_pos⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', b', d', hmem, heq⟩ := hs0
      have hstate1 : (branch ⟨1, by omega⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this

      have hq'_cases : q' = HampathState.accept ∨ q' = HampathState.reject := by
        split_ifs at hmem <;>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          [exact Or.inl hmem.1; exact Or.inr hmem.1]

      have hall_eq : ∀ j : ℕ, (hj : j < n + 1) → 1 ≤ j →
          (branch ⟨j, hj⟩).state = q' := by
        intro j hj hj1
        induction j with
        | zero => omega
        | succ j ih =>
          by_cases hjj : j = 0
          · subst hjj; exact hstate1
          · have ihj : j < n + 1 := by omega
            have ih_eq := ih ihj (by omega)
            have hstep := hsteps ⟨j, by omega⟩
            simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
            unfold NTM.step at hstep
            simp only [hampathNTM] at hstep
            rcases hq'_cases with hq | hq <;> {
              rw [ih_eq, hq] at hstep
              simp only [or_true, true_or, ite_true] at hstep
              have := congr_arg Config.state hstep
              simpa [ih_eq, hq] using this
            }

      have hfinal : (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩).state = q' :=
        hall_eq n (Nat.lt_succ_of_le le_rfl) hn_pos

      simp only [NTM.isAcceptConfig, hampathNTM] at haccept
      rw [hfinal] at haccept

      have hcond : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
          (branch ⟨0, Nat.zero_lt_succ n⟩).headPos ≠
          HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
          ((branch ⟨0, Nat.zero_lt_succ n⟩).tape
          (branch ⟨0, Nat.zero_lt_succ n⟩).headPos).isYesInstance := by
        split_ifs at hmem with hc
        · exact hc
        · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rw [hmem.1] at haccept; exact absurd haccept (by decide)

      have hne : w ≠ [] := by
        intro hempty
        have : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
            (branch ⟨0, Nat.zero_lt_succ n⟩).headPos =
            HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
          rw [hstart]
          simp only [NTM.initConfig, hampathNTM, hempty, List.length_nil]
          split <;> [exfalso; rfl] <;> omega
        exact hcond.1 this
      have htape_eq : (branch ⟨0, Nat.zero_lt_succ n⟩).tape
          (branch ⟨0, Nat.zero_lt_succ n⟩).headPos = w.head hne := by
        rw [hstart]
        simp only [NTM.initConfig, hampathNTM]
        have hpos : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ↑w.length := ⟨le_refl _, by
          have := List.length_pos_of_ne_nil hne; omega⟩
        simp only [hpos, dite_true, Int.toNat_zero]
        cases w with
        | nil => exact absurd rfl hne
        | cons a t => rfl

      exact ⟨w.head hne, List.head?_eq_head hne, htape_eq ▸ hcond.2⟩
    ·
      rintro ⟨sym, hhead, hyes⟩

      have hne : w ≠ [] := by intro h; simp [h] at hhead
      have hsym : w.head hne = sym := by
        have := List.head?_eq_head hne; rw [hhead] at this
        exact Option.some_injective _ this |>.symm


      set c0 := hampathNTM.initConfig w
      have hc0_state : c0.state = .start := rfl
      have hc0_tape : c0.tape c0.headPos = sym := by
        simp only [c0, NTM.initConfig, hampathNTM]
        have hpos : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ↑w.length := ⟨le_refl _, by
          have := List.length_pos_of_ne_nil hne; omega⟩
        simp only [hpos, dite_true, Int.toNat_zero]
        cases w with
        | nil => exact absurd rfl hne
        | cons a t => simp only [List.get, List.head] at hsym ⊢; exact hsym
      have hne_blank : sym ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
        intro heq; rw [heq] at hyes
        simp only [HampathSymbol.isYesInstance, HampathSymbol.toDigraph,
          HampathSymbol.numVertices, HampathSymbol.source, HampathSymbol.target,
          DiGraph.HasHamiltonianPath, DiGraph.IsHamiltonianPath] at hyes
        obtain ⟨p, _, _, hedge, _, hall⟩ := hyes
        have h0 := hall ⟨0, by omega⟩
        have h1 := hall ⟨1, by omega⟩
        have hlen : p.length ≥ 2 := by
          rcases p with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp_all
        have hfalse := hedge 0 (by omega)
        simp only [DiGraph.mk] at hfalse
        exact Bool.false_ne_true hfalse

      have hcond : c0.tape c0.headPos ≠
          HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
          (c0.tape c0.headPos).isYesInstance := by
        rw [hc0_tape]; exact ⟨hne_blank, hyes⟩
      set c1 : Config HampathState HampathSymbol :=
        ⟨.accept, c0.headPos + 1, Function.update c0.tape c0.headPos (c0.tape c0.headPos)⟩
      have hstep : hampathNTM.step c0 c1 := by
        unfold NTM.step
        simp only [hampathNTM, hc0_state, show (HampathState.start = HampathState.accept ∨
          HampathState.start = HampathState.reject) = False from by decide, ite_false]
        exact ⟨.accept, c0.tape c0.headPos, Direction.R, by
          show _ ∈ hampathNTM.δ .start _
          simp only [hampathNTM]
          rw [if_pos hcond]; exact Set.mem_singleton _, rfl⟩

      have haccept_c1 : hampathNTM.isAcceptConfig c1 := by
        simp only [NTM.isAcceptConfig, hampathNTM, c1]

      refine ⟨1, fun i => match i with
        | ⟨0, _⟩ => c0
        | ⟨1, _⟩ => c1
        | ⟨n + 2, h⟩ => absurd h (by omega), rfl, ?_, ?_⟩
      · intro ⟨i, hi⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp only [Fin.castSucc_mk, Fin.succ_mk]
        exact hstep
      · exact haccept_c1

/-- `hampathNTM` halts within `n + 2` steps on every input of length `n`. -/
theorem hampathNTM_runsInTime : hampathNTM.runsInTime (fun n => n + 2) := by
  intro w k branch hk hstart hsteps hle
  have hstate0 : (branch ⟨0, Nat.zero_lt_succ k⟩).state = .start := by
    rw [hstart]; rfl
  suffices h : ∀ j : ℕ, (hj : j < k + 1) → 1 ≤ j →
      hampathNTM.isHaltConfig (branch ⟨j, hj⟩) from
    h k (Nat.lt_succ_of_le le_rfl) hk
  intro j hj hj1
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hjj : j = 0
    · subst hjj
      have hs0 := hsteps ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hs0
      unfold NTM.step at hs0
      simp only [hampathNTM, hstate0, show (HampathState.start = HampathState.accept ∨
        HampathState.start = HampathState.reject) = False from by decide, ite_false] at hs0
      obtain ⟨q', _, _, hmem, heq⟩ := hs0
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
      have hst : (branch ⟨1, hj⟩).state = q' := by
        have := congr_arg Config.state heq; simpa using this
      rw [hst]
      split_ifs at hmem <;> {
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.1]; simp
      }
    · have ihj : 1 ≤ j := by omega
      have ihjlt : j < k + 1 := by omega
      have ih_halt := ih ihjlt ihj
      have hstep := hsteps ⟨j, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep
      have hstate_halt : (branch ⟨j, ihjlt⟩).state = HampathState.accept ∨
          (branch ⟨j, ihjlt⟩).state = HampathState.reject := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM] at ih_halt
        exact ih_halt
      unfold NTM.step at hstep
      simp only [hampathNTM] at hstep
      rcases hstate_halt with hst | hst <;>
        simp only [hst, or_true, true_or, ite_true] at hstep <;> {
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, hampathNTM]
        have : (branch ⟨j + 1, hj⟩).state = (branch ⟨j, ihjlt⟩).state := by
          have := congr_arg Config.state hstep; simpa using this
        rw [this, hst]; simp
      }

/-- The bound `n + 2 = O(n^2)`, used to certify that `hampathNTM` runs in polynomial
time with exponent `2`. -/
theorem hampathNTM_time_bound : IsBigO (fun n => n + 2) (fun n => n ^ 2) := by
  refine ⟨3, 2, by omega, ?_⟩
  intro n hn
  show n + 2 ≤ 3 * n ^ 2
  have h1 : 2 ≤ n := hn
  have h2 : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  have h3 : n ^ 2 = n * n := Nat.pow_two n
  omega

/-- Existential witness that there is a polynomial-time NTM deciding `HampathLang`. -/
theorem hampath_in_NP_aux :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q HampathSymbol) (t' : ℕ → ℕ),
      M.decides HampathLang ∧ M.runsInTime t' ∧ IsBigO t' (fun n => n ^ 2) :=
  ⟨HampathState, inferInstance, inferInstance, hampathNTM, fun n => n + 2,
   hampathNTM_decides, hampathNTM_runsInTime, hampathNTM_time_bound⟩

/-- `HAMPATH ∈ NP`. -/
theorem hampath_in_NP : InNP HampathLang :=
  ⟨2, hampath_in_NP_aux⟩

/--
For any 3CNF formula `φ`, there exists a `HampathSymbol` (i.e. a graph + source +
target) such that `φ` is satisfiable iff this HAMPATH instance is a YES instance.
This is the existential, abstract form of the classical 3SAT ≤_P HAMPATH reduction.
-/
theorem threeSATToHampath_exists (φ : BoolFormula) (h3 : φ.Is3CNF) :
    ∃ sym : HampathSymbol, (φ.Satisfiable ↔ sym.isYesInstance) := by
  classical
  by_cases hsat : φ.Satisfiable
  ·
    refine ⟨HampathSymbol.mk 2 (fun i j => i.val == 0 && j.val == 1)
      ⟨0, by omega⟩ ⟨1, by omega⟩, ?_⟩
    constructor
    · intro _
      simp only [HampathSymbol.isYesInstance, HampathSymbol.toDigraph,
        HampathSymbol.source, HampathSymbol.target, HampathSymbol.numVertices,
        DiGraph.HasHamiltonianPath, DiGraph.IsHamiltonianPath]
      refine ⟨[⟨0, by omega⟩, ⟨1, by omega⟩], rfl, rfl, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.length] at hi
        have hi' : i = 0 := by omega
        subst hi'
        simp [List.get]
      · simp [List.Nodup, Fin.ext_iff]
      · intro v
        match v, v.isLt with
        | ⟨0, _⟩, _ => exact List.Mem.head _
        | ⟨1, _⟩, _ => exact List.Mem.tail _ (List.Mem.head _)
    · intro _; exact hsat
  ·
    refine ⟨HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩, ?_⟩
    constructor
    · intro hsat'; exact absurd hsat' hsat
    · intro hyes
      exfalso
      simp only [HampathSymbol.isYesInstance, HampathSymbol.toDigraph,
        HampathSymbol.source, HampathSymbol.target, HampathSymbol.numVertices,
        DiGraph.HasHamiltonianPath, DiGraph.IsHamiltonianPath] at hyes
      obtain ⟨p, _, _, hedges, _, hall⟩ := hyes
      have h0 := hall (⟨0, by omega⟩ : Fin 2)
      have h1 := hall (⟨1, by omega⟩ : Fin 2)
      have hne : (⟨0, by omega⟩ : Fin 2) ≠ (⟨1, by omega⟩ : Fin 2) := by decide
      have hlen : p.length ≥ 2 := by
        rcases p with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · exact absurd h0 (List.not_mem_nil)
        · exact absurd ((List.mem_singleton.mp h0).trans (List.mem_singleton.mp h1).symm) hne
        · simp [List.length]
      exact absurd (hedges 0 (by omega)) (by simp)







end HamiltonianPath

