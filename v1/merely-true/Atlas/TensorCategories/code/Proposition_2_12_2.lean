/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorAbelianDefs
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.InducedCategory

set_option maxHeartbeats 800000
set_option linter.all false

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

/-- A right-exact module functor between left `C`-module categories `M₁` and `M₂`:
a module functor whose underlying functor sends epimorphisms to epimorphisms. -/
structure RightExactModuleFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂]
    extends ModuleFunctor C M₁ M₂ where
  preserves_epi : ∀ {A B : M₁} (f : A ⟶ B), Epi f → Epi (toFunctor.map f)

/-- The category structure on right-exact module functors, induced from the
ambient category of module functors via the forgetful map. -/
instance rightExactModuleFunctorCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (N : Type u₃) [Category.{v₃} N] [LeftModuleCategory C N] :
    Category (RightExactModuleFunctor C M N) :=
  inferInstanceAs (Category (InducedCategory _ RightExactModuleFunctor.toModuleFunctor))



end CategoryTheory
