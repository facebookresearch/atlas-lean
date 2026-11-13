/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.NumberTheoryI.code.Lem1812

open DirichletCharacter MulChar


theorem cor_18_15 {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    ∑ n : ZMod m, χ n ≠ 0 ↔ χ.conductor = 1 := by
  rw [lem_18_12 χ, eq_one_iff_conductor_eq_one (NeZero.ne m)]
