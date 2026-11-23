/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open MonoidalCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- An algebra in a multitensor category `C` is a triple `(A, m, u)` where `A` is an object
of `C` and `m : A ⊗ A → A`, `u : 1 → A` are morphisms (multiplication and unit) satisfying
associativity and unit axioms. Implemented as the Mathlib type `Mon C` of monoid objects. -/
abbrev Definition_2_9_1 := Mon C

end CategoryTheory
