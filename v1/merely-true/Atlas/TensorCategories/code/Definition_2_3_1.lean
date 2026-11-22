/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open CategoryTheory CategoryTheory.Limits
open LeftModCat

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

/-- Definition 2.3.1: an `AbelianModuleCategory` is an abelian, `k`-linear module
category `M` over a `k`-linear monoidal category `C` with finite-dimensional hom-spaces,
artinian and noetherian objects, and action functors that are linear, exact, and
preserve finite (co)limits in the first variable. -/
class AbelianModuleCategory
    (k : Type*) [Field k]
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [Preadditive C] [Linear k C]
    (M : Type u₂) [Category.{v₂} M] where
  [abelian : Abelian M]
  [linear : Linear k M]
  finiteDimHom : ∀ (X Y : M), Module.Finite k (X ⟶ Y)
  artinian : ∀ (X : M), IsArtinianObject X
  noetherian : ∀ (X : M), IsNoetherianObject X
  [moduleStruct : LeftModuleCategoryStruct C M]
  [moduleCategory : LeftModuleCategory C M]
  actFirstVarFunctor : ∀ (N : M), C ⥤ M
  actFirstVarFunctor_obj : ∀ (N : M) (X : C),
    (actFirstVarFunctor N).obj X = X ⊗ᵐ N
  actFirstVar_linear : ∀ (N : M), Functor.Linear k (actFirstVarFunctor N)
  actFirstVar_preservesFiniteLimits : ∀ (N : M),
    PreservesFiniteLimits (actFirstVarFunctor N)
  actFirstVar_preservesFiniteColimits : ∀ (N : M),
    PreservesFiniteColimits (actFirstVarFunctor N)
  actSecondVarFunctor : ∀ (X : C), M ⥤ M
  actSecondVarFunctor_obj : ∀ (X : C) (N : M),
    (actSecondVarFunctor X).obj N = X ⊗ᵐ N
  actSecondVar_additive : ∀ (X : C), (actSecondVarFunctor X).Additive
  actSecondVar_linear : ∀ (X : C), Functor.Linear k (actSecondVarFunctor X)

attribute [instance] AbelianModuleCategory.abelian
attribute [instance] AbelianModuleCategory.linear
attribute [instance] AbelianModuleCategory.moduleStruct
attribute [instance] AbelianModuleCategory.moduleCategory

/-- Definition 2.3.1 (alias): a module category satisfying the abelian, linear,
finiteness, and exactness conditions packaged in `AbelianModuleCategory`. -/
abbrev Definition_2_3_1 := @AbelianModuleCategory

/-- Convenience alias for `AbelianModuleCategory`. -/
abbrev IsAbelianModuleCategory := @AbelianModuleCategory

end CategoryTheory
