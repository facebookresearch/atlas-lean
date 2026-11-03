/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory

set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.ExactModuleCategory MonoidalCategory Limits

universe u₁ v₁ u₂ v₂

/-- The subtype of simple objects of `M`, packaging an object together with its `Simple` instance. -/
abbrev SimpleObj (M : Type u₂) [Category.{v₂} M] [HasZeroMorphisms M] :=
  { X : M // Simple X }

/-- The relation on simple objects of a left `C`-module category which holds when one is a
subquotient of `X ⊗ Y` for some `X ∈ C`; this is the equivalence used to decompose an exact
module category. -/
def subquotientRelation
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] [HasZeroMorphisms M] :
    SimpleObj M → SimpleObj M → Prop :=
  fun X Y => IrrRelated C M X.val Y.val
