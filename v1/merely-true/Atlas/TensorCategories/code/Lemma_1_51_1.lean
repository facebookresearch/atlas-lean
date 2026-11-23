/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

open CategoryTheory MonoidalCategory Category

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An object `X` of a monoidal category is invertible (in the sense of Section 1.51) if there
exists a tensor inverse `tensorInverse` and isomorphisms exhibiting `X ⊗ tensorInverse ≅ 𝟙_ C`
and `tensorInverse ⊗ X ≅ 𝟙_ C`. -/
class IsInvertibleObject_1_51 (X : C) where
  tensorInverse : C
  compIso : X ⊗ tensorInverse ≅ 𝟙_ C
  invCompIso : tensorInverse ⊗ X ≅ 𝟙_ C

variable [RigidCategory C]

/-- The double right dual `X**` of an object `X` in a rigid monoidal category, used in
Section 1.51 of EGNO. -/
def doubleDual_1_51 (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)

variable (C) in
/-- Data witnessing the existence of a distinguished invertible object in `C`, packaging
a chosen object `distinguished : C` together with isomorphisms `P** ≅ distinguished ⊗ P` for
every projective `P` and a self-isomorphism `distinguished** ≅ distinguished`. This is the
hypothesis structure for Lemma 1.51.1 of EGNO. -/
class HasDistinguishedInvertibleData_1_51 where
  distinguished : C
  doubleDual_iso_tensor : ∀ (P : C) [Projective P],
    Nonempty (doubleDual_1_51 P ≅ distinguished ⊗ P)
  doubleDual_self : Nonempty (doubleDual_1_51 distinguished ≅ distinguished)


end CategoryTheory
