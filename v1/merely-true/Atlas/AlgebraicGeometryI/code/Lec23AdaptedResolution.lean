/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors

open CategoryTheory Category Limits

noncomputable section

universe v u

namespace Lec23AdaptedResolution



/-- Every injective object is adjusted to any additive functor: `RⁿF` vanishes on
injectives for `n > 0`. -/
theorem injective_is_adjusted
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) [Injective M] :
    Lec23.IsAdjustedToFunctor F M :=
  Lec23.injective_isAdjustedToFunctor F M

/-- The standard identification of the right derived functor as the cohomology of `F`
applied to an injective resolution. -/
noncomputable def prop43_injective_resolution_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

/-- Independence of injective resolution: the cohomology of `F` applied to two different
injective resolutions of `X` is canonically isomorphic. -/
noncomputable def prop43_resolution_uniqueness
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ)
    {X : C} (I J : InjectiveResolution X) :
    (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj J.cocomplex) :=
  (I.isoRightDerivedObj F n).symm ≪≫ J.isoRightDerivedObj F n

end Lec23AdaptedResolution
