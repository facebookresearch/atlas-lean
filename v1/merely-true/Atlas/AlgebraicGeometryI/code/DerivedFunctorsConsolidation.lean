/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Atlas.AlgebraicGeometryI.code.RightDerivedDelta
import Atlas.AlgebraicGeometryI.code.EffaceableUniversal

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedFunctorsDefs CohomologyConnection

universe v u


section PartA

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- For a left-exact additive functor `F : C ⥤ D`, the zeroth right derived functor of `F`
evaluated at `X` is naturally isomorphic to `F.obj X`. -/
def rightDerivedZero_obj_iso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (X : C) : (F.rightDerived 0).obj X ≅ F.obj X :=
  F.rightDerivedZeroIsoSelf.app X

end PartA


section PartB

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- For an additive functor `F`, the positive-degree right derived functors vanish on
injective objects: `R^n F (X) = 0` for `n > 0` and `X` injective. -/
theorem rightDerived_injective_is_zero (F : C ⥤ D) [F.Additive]
    (n : ℕ) (X : C) [Injective X] (hn : 0 < n) :
    IsZero ((F.rightDerived n).obj X) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact F.isZero_rightDerived_obj_injective_succ k X

end PartB


section PartC

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- Placeholder statement that the right derived functors of `F` are independent of the
chosen injective resolution. -/
structure ResolutionIndependence (F : C ⥤ D) [F.Additive] : Prop where
  obj_determined : ∀ (n : ℕ) (X : C),
    ∃! (_ : (F.rightDerived n).obj X = (F.rightDerived n).obj X), True

end PartC


section PartD

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Uniqueness part of universality: any two morphisms of δ-functors out of an effaceable
δ-functor `T` that agree in degree zero must agree in every degree. -/
theorem effaceable_implies_universal_uniqueness
    (T : CohomDeltaFunctor C D) (hT : T.IsEffaceable) :
    ∀ (G : CohomDeltaFunctor C D) (m₁ m₂ : T.Morphism G),
      m₁.η 0 = m₂.η 0 → ∀ n, m₁.η n = m₂.η n :=
  fun G m₁ m₂ h₀ => effaceable_morphism_unique T G hT m₁ m₂ h₀



end PartD


section PartE

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end PartE
