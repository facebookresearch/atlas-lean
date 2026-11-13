/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Bimod

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An `(A,B)`-bimodule in a monoidal category `C`: an object equipped with commuting left
`A`-action and right `B`-action. -/
abbrev Bimodule (A B : Mon C) := Bimod A B

/-- The underlying object of an `(A,B)`-bimodule. -/
abbrev Bimodule.obj {A B : Mon C} (M : Bimodule A B) : C := M.X

/-- The left `A`-action morphism `A ⊗ M → M` of an `(A,B)`-bimodule. -/
abbrev Bimodule.leftAction {A B : Mon C} (M : Bimodule A B) : A.X ⊗ M.X ⟶ M.X :=
  M.actLeft

/-- The right `B`-action morphism `M ⊗ B → M` of an `(A,B)`-bimodule. -/
abbrev Bimodule.rightAction {A B : Mon C} (M : Bimodule A B) : M.X ⊗ B.X ⟶ M.X :=
  M.actRight

/-- The middle-associativity (bimodule compatibility) axiom: the left and right actions
on a bimodule commute up to the associator. -/
theorem Bimodule.actions_commute {A B : Mon C} (M : Bimodule A B) :
    M.actLeft ▷ B.X ≫ M.actRight =
      (α_ A.X M.X B.X).hom ≫ A.X ◁ M.actRight ≫ M.actLeft :=
  M.middle_assoc

end CategoryTheory
