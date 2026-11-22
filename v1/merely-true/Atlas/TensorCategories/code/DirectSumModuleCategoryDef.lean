/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace DirectSumModuleCat

open Category MonoidalCategory Limits

/-- Predicate-style data witnessing that a `C`-module category `M` is the direct sum
of two `C`-module categories `M₁` and `M₂`: full and faithful inclusions of `M₁` and
`M₂` into `M` such that every object of `M` decomposes uniquely as a biproduct of an
object from each summand. -/
structure IsDirectSumModuleCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [HasZeroMorphisms M] [HasBinaryBiproducts M]
    [LeftModuleCategory C M]
    (M₁ : Type u₃) [Category.{v₃} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₄) [Category.{v₄} M₂] [LeftModuleCategory C M₂] where
  incl₁ : M₁ ⥤ M
  incl₂ : M₂ ⥤ M
  full₁ : incl₁.Full
  full₂ : incl₂.Full
  faithful₁ : incl₁.Faithful
  faithful₂ : incl₂.Faithful
  decomp : ∀ (X : M), ∃! (p : M₁ × M₂),
    Nonempty (X ≅ incl₁.obj p.1 ⊞ incl₂.obj p.2)

end DirectSumModuleCat

end CategoryTheory
