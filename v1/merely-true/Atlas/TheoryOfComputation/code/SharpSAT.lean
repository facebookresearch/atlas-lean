/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.NPCompleteness
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi

namespace NPCompleteness

/--
The (finite) set of variable indices occurring in a Boolean formula `φ`.
Recursively collected: variables of constants are empty, of `var n` is `{n}`,
and of compound formulas is the union of subformulas' variable sets.
-/
def BoolFormula.vars : BoolFormula → Finset ℕ
  | .var n => {n}
  | .trueConst => ∅
  | .falseConst => ∅
  | .not φ => φ.vars
  | .and φ ψ => φ.vars ∪ ψ.vars
  | .or φ ψ => φ.vars ∪ ψ.vars

/-- The number of distinct variables occurring in `φ`. -/
def BoolFormula.numVars (φ : BoolFormula) : ℕ := φ.vars.card

/--
The number of satisfying assignments of `φ`, where assignments range over
Boolean valuations of the variables actually occurring in `φ`. Variables not in
`φ.vars` are set to `false` (and do not affect the truth value by
`eval_eq_of_agree_on_vars`).
-/
noncomputable def BoolFormula.countSat (φ : BoolFormula) : ℕ :=
  Finset.card (Finset.univ.filter (fun (σ : φ.vars → Bool) =>
    φ.eval (fun i => if h : i ∈ φ.vars then σ ⟨i, h⟩ else false) = true))

/-- The `#SAT` count of `φ`: the number of satisfying assignments of `φ`. Alias
for `countSat`. -/
noncomputable def BoolFormula.sharpSat (φ : BoolFormula) : ℕ :=
  φ.countSat

/--
The `#SAT` language as a set of pairs `⟨φ, k⟩`:
`#SAT = {⟨φ, k⟩ | φ has exactly k satisfying assignments}` (Sipser, Lecture 25).
-/
noncomputable def SharpSAT : Set (BoolFormula × ℕ) :=
  {p | p.2 = p.1.sharpSat}

end NPCompleteness
