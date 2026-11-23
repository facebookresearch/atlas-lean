/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- A Carmichael number is a composite natural number `n > 1` such that
`a ^ n = a` in `ZMod n` for every `a`, i.e. it satisfies the conclusion of
Fermat's little theorem despite not being prime. -/
def IsCarmichaelNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ZMod n, a ^ n = a

