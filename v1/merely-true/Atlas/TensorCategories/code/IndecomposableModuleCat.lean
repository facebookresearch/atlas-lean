/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DirectSumModuleCategory
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

set_option maxHeartbeats 800000

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

/-- A category is a zero category if every one of its objects is a zero object. -/
def IsZeroCategory (M : Type*) [Category M] : Prop :=
  ∀ X : M, Limits.IsZero X

/-- A module category `M` over a monoidal category `C` is indecomposable if whenever it is
equivalent (as a `C`-module category) to a direct sum `M₁ × M₂`, one of the summands is empty. -/
class IsIndecomposableModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  indecomp : ∀ (M₁ M₂ : Type u₂) [Category.{v₂} M₁] [Category.{v₂} M₂]
    [LeftModuleCategory C M₁] [LeftModuleCategory C M₂]
    (_ : ModuleEquivalence C M (M₁ × M₂)), IsEmpty M₁ ∨ IsEmpty M₂

/-- Definition 2.4.3: a module category `M` over `C` is indecomposable if it is not equivalent
to a nontrivial direct sum of module categories (with both summands nonzero). -/
abbrev Definition_2_4_3 := @IsIndecomposableModuleCategory

end CategoryTheory
