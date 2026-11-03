/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory

namespace Deligne

section CategoricalFramework

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- For a fixed object `d : D`, the functor `C ⥤ C × D` sending `c ↦ (c, d)` and
`f ↦ (f, 𝟙 d)`. Used to express right exactness of bifunctors in the first variable. -/
def sliceFunctorRight {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (d : D) : C ⥤ C × D where
  obj c := (c, d)
  map f := (f, 𝟙 d)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-- For a fixed object `c : C`, the functor `D ⥤ C × D` sending `d ↦ (c, d)` and
`g ↦ (𝟙 c, g)`. Used to express right exactness of bifunctors in the second variable. -/
def sliceFunctorLeft {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (c : C) : D ⥤ C × D where
  obj d := (c, d)
  map g := (𝟙 c, g)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-- A bifunctor `F : C × D ⥤ E` is right exact when it is right exact in each variable,
i.e. the slice functors `sliceFunctorRight d ⋙ F` and `sliceFunctorLeft c ⋙ F` preserve
finite colimits. -/
structure IsRightExactBifunctor {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    (F : C × D ⥤ E) : Prop where
  rightExactInFirst : ∀ (d : D), Limits.PreservesFiniteColimits (sliceFunctorRight d ⋙ F)
  rightExactInSecond : ∀ (c : C), Limits.PreservesFiniteColimits (sliceFunctorLeft c ⋙ F)

/-- A bifunctor `F : C × D ⥤ E` between `k`-linear preadditive categories is bilinear
when it is `k`-linear in each variable. -/
structure IsBilinearBifunctor
    (k : Type w) [Field k]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]
    {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear k E]
    (F : C × D ⥤ E) : Prop where
  linearInFirst : ∀ (d : D), Functor.Linear k (sliceFunctorRight d ⋙ F)
  linearInSecond : ∀ (c : C), Functor.Linear k (sliceFunctorLeft c ⋙ F)

/-- A bifunctor `F : C × D ⥤ E` is right-exact bilinear when it is both bilinear in each
variable and right exact in each variable. -/
structure IsRightExactBilinearBifunctor
    (k : Type w) [Field k]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]
    {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear k E]
    (F : C × D ⥤ E) : Prop where
  bilinear : IsBilinearBifunctor k F
  rightExact : IsRightExactBifunctor F

/-- Definition 1.46.1: Deligne's tensor product `C ⊠ D`. A witness consisting of a
`k`-linear abelian category `tensorCat` together with a right-exact bilinear bifunctor
`⊠ : C × D ⥤ tensorCat` that is universal among such bifunctors out of `C × D`. Any
right-exact bilinear bifunctor `F : C × D ⥤ A` factors through `⊠` via an essentially
unique right-exact `k`-linear functor `F_bar : tensorCat ⥤ A`. -/
structure HasDeligneTensorProduct
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [Linear k C]
    (D : Type u₂) [Category.{v₂} D] [Abelian D] [Linear k D] where
  tensorCat : Type u₃
  [categoryInst : Category.{v₃} tensorCat]
  [abelianInst : Abelian tensorCat]
  [linearInst : Linear k tensorCat]
  boxtimesFunctor : C × D ⥤ tensorCat
  boxtimes_bilinearRightExact : IsRightExactBilinearBifunctor k boxtimesFunctor
  factor : ∀ {A : Type u₃} [Category.{v₃} A] [Abelian A] [Linear k A]
    (F : C × D ⥤ A),
    IsRightExactBilinearBifunctor k F →
    ∃ (F_bar : tensorCat ⥤ A),
      Limits.PreservesFiniteColimits F_bar ∧
      Functor.Linear k F_bar ∧
      Nonempty (boxtimesFunctor ⋙ F_bar ≅ F)
  factor_unique : ∀ {A : Type u₃} [Category.{v₃} A] [Abelian A] [Linear k A]
    (_F : C × D ⥤ A) (G₁ G₂ : tensorCat ⥤ A),
    Limits.PreservesFiniteColimits G₁ → Limits.PreservesFiniteColimits G₂ →
    Functor.Linear k G₁ → Functor.Linear k G₂ →
    Nonempty (boxtimesFunctor ⋙ G₁ ≅ boxtimesFunctor ⋙ G₂) →
    Nonempty (G₁ ≅ G₂)

attribute [instance] HasDeligneTensorProduct.categoryInst
attribute [instance] HasDeligneTensorProduct.abelianInst
attribute [instance] HasDeligneTensorProduct.linearInst

end CategoricalFramework

end Deligne

end
