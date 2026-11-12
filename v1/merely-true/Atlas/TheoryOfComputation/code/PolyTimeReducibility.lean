/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.Complexity

open TuringMachine

/-- **Sipser, Lecture 14.** Polynomial-time mapping reducibility `A ≤_P B`:
`A` reduces to `B` via a polynomial-time computable function `f` with
`w ∈ A ↔ f w ∈ B`. (Alias for `TuringMachine.PolyReducible`.) -/
abbrev PolyTimeReducible {Γ : Type} (A B : Set (List Γ)) : Prop :=
  TuringMachine.PolyReducible A B

