/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option linter.unusedSimpArgs false

universe u v

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open HasLeftDual HasRightDual ExactPairing MonObj

namespace Lemma2147

/-- The canonical algebra multiplication on `ᘁA ⊗ A` for an object `A` with a left dual,
defined by inserting the evaluation `ε_ (ᘁA) A` in the middle. -/
noncomputable def dualAlgMul (A : C) [HasLeftDual A] :
    ((ᘁA : C) ⊗ A) ⊗ ((ᘁA : C) ⊗ A) ⟶ (ᘁA : C) ⊗ A :=
  (α_ (ᘁA : C) A ((ᘁA : C) ⊗ A)).hom ≫
  (ᘁA : C) ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)

/-- A left module object over an algebra `B` in `C`: an object `Y` equipped with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

/-- A right module object over an algebra `B` in `C`: an object `Y` equipped with an action
`Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act










end Lemma2147


end CategoryTheory
