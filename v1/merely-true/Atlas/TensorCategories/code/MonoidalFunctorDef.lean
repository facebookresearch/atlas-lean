/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TensorCategories

/-- EGNO Definition 1.1.2: a monoidal subcategory of `C` is a category `D` with a
faithful monoidal functor `ι : D ⥤ C`. -/
structure def_1_1_2_MonoidalSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] where
  D : Type u₂
  [instCat : Category.{v₂} D]
  [instMonoidal : MonoidalCategory D]
  ι : D ⥤ C
  [instFaithful : ι.Faithful]
  instMonoidalFunctor : ι.Monoidal

attribute [instance] def_1_1_2_MonoidalSubcategory.instCat
  def_1_1_2_MonoidalSubcategory.instMonoidal
  def_1_1_2_MonoidalSubcategory.instFaithful

/-- Construct a monoidal subcategory in the sense of EGNO Definition 1.1.2 from any
monoidal `ObjectProperty` on `C`, using the inclusion of the corresponding full
subcategory. -/
def def_1_1_2_MonoidalSubcategory.ofFullSubcategory
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] :
    def_1_1_2_MonoidalSubcategory.{v₁, v₁, u₁, u₁} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

section MonoidalFunctor

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.1: a monoidal functor `C ⥤ D` is a functor `F` together with the
data of a monoidal structure on `F`. -/
structure def_1_4_1_MonoidalFunctor where
  F : C ⥤ D
  instMonoidal : F.Monoidal

attribute [instance] def_1_4_1_MonoidalFunctor.instMonoidal

/-- The monoidal structure morphism `J : F X ⊗ F Y ≅ F (X ⊗ Y)` of EGNO Definition 1.4.1,
extracted from the underlying `Functor.Monoidal` instance. -/
def def_1_4_1_MonoidalFunctor.J {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (MF : def_1_4_1_MonoidalFunctor C D) (X Y : C) :
    MF.F.obj X ⊗ MF.F.obj Y ≅ MF.F.obj (X ⊗ Y) :=
  @Functor.Monoidal.μIso _ _ _ _ _ _ MF.F MF.instMonoidal X Y

end MonoidalFunctor

section MonoidalNatTrans

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.5: a monoidal functor on `F`, expressed as the existence of a
`Functor.Monoidal` structure. -/
abbrev def_1_4_5_MonoidalFunctor (F : C ⥤ D) := F.Monoidal

/-- EGNO Definition 1.5.1: a monoidal natural transformation between lax monoidal
functors, expressed via `NatTrans.IsMonoidal`. -/
abbrev def_1_5_1_MonoidalNatTrans {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) :=
  NatTrans.IsMonoidal η

/-- EGNO Definition 1.5.1 (isomorphism version): an isomorphism of lax monoidal functors. -/
abbrev def_1_5_1_MonoidalFunctorIso (F G : LaxMonoidalFunctor C D) :=
  F ≅ G

end MonoidalNatTrans

end TensorCategories
