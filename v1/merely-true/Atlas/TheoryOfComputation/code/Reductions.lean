/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.TuringMachines
namespace TuringMachine

open TuringMachine

variable {Γ : Type}

/-- Read the first `n` cells of the tape of configuration `c` as a list. -/
def Config.readTape (c : Config Q Γ) (n : ℕ) : List Γ :=
  (List.range n).map (fun i => c.tape ((i : ℕ) : ℤ))

/-- A function `f : Σ* → Σ*` is (Turing-)computable if there is a TM `F` that,
on every input `w`, halts with the string `f w` written as the prefix of its
tape. -/
def IsComputableFunction (f : List Γ → List Γ) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (F : TM Q Γ),
    ∀ w : List Γ, ∃ n : ℕ,
      F.isHaltConfig (F.runOnInput w n) ∧
      Config.readTape (F.runOnInput w n) (f w).length = f w

/-- Mapping reducibility `A ≤ₘ B`: there is a computable function `f` with
`w ∈ A ↔ f w ∈ B` (Sipser, Lecture 9). -/
def MappingReducible (A B : Set (List Γ)) : Prop :=
  ∃ f : List Γ → List Γ,
    IsComputableFunction f ∧
    ∀ w : List Γ, w ∈ A ↔ f w ∈ B

/-- Notation `A ≤ₘ B` for mapping reducibility. -/
scoped infixl:50 " ≤ₘ " => MappingReducible


end TuringMachine


namespace TuringMachine


end TuringMachine
