/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.NumberTheoryI.code.ArithmeticFunctions
import Atlas.NumberTheoryI.code.Cor1838

open DirichletCharacter MulChar


theorem lem_18_12 {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    ∑ n : ZMod m, χ n ≠ 0 ↔ χ = 1 := by
  constructor
  · intro h
    by_contra hχ
    exact h (MulChar.sum_eq_zero_of_ne_one hχ)
  · intro h
    subst h
    classical
    rw [MulChar.sum_one_eq_card_units]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
