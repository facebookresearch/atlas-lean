/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section

open CategoryTheory Category Limits

universe v u

namespace AdjustedResolutions

/-- An object `M` is *adjusted to* an additive functor `F` if all higher right derived functors
of `F` vanish on `M`: `RⁱF(M) = 0` for `i > 0`. Such objects (e.g. injectives, or `F`-acyclic
objects) can be used in place of injective resolutions when computing `RF`. -/
def IsAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) : Prop :=
  ∀ (i : ℕ), 0 < i → IsZero ((F.rightDerived i).obj M)

/-- A *resolution* of an object `M` in an abelian category: a cochain complex `K•` together with a
quasi-isomorphism `M[0] → K•` from the complex concentrated in degree zero. -/
structure Resolution {C : Type u} [Category.{v} C] [Abelian C] (M : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj M ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- Every injective resolution is in particular a resolution. -/
def InjectiveResolution.toResolution
    {C : Type u} [Category.{v} C] [Abelian C] {M : C}
    (I : InjectiveResolution M) : Resolution M where
  cocomplex := I.cocomplex
  ι := I.ι

/-- Any injective object is adjusted to every additive functor: `RⁱF(M) = 0` for `i > 0` when
`M` is injective. -/
theorem injective_isAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) [Injective M] :
    IsAdjustedToFunctor F M := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k M

/-- Every object in an injective resolution is adjusted to any additive functor `F`. -/
theorem injRes_objects_adjusted
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M : C} (I : InjectiveResolution M) (n : ℕ) :
    IsAdjustedToFunctor F (I.cocomplex.X n) :=
  injective_isAdjustedToFunctor F (I.cocomplex.X n)



/-- Specialization of Prop 43 to an injective resolution: `RⁿF(X) ≃ Hⁿ(F(I•))`. -/
noncomputable def prop43_injective_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

/-- Independence of the choice of injective resolution: two injective resolutions of `X` give
canonically isomorphic computations of `RⁿF(X)`. -/
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

end AdjustedResolutions
