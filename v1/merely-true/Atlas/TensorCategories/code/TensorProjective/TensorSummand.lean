/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Retract

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace CategoryTheory.Retract

/-- Tensoring a retract `P` of `Q` on the left by `X` yields a retract `X ⊗ P` of `X ⊗ Q`. -/
def tensorLeft (X : C) {P Q : C} (h : Retract P Q) :
    Retract (X ⊗ P) (X ⊗ Q) :=
  h.map (MonoidalCategory.tensorLeft X)

/-- Tensoring a retract `P` of `Q` on the right by `X` yields a retract `P ⊗ X` of `Q ⊗ X`. -/
def tensorRight {P Q : C} (h : Retract P Q) (X : C) :
    Retract (P ⊗ X) (Q ⊗ X) :=
  h.map (MonoidalCategory.tensorRight X)

end CategoryTheory.Retract
