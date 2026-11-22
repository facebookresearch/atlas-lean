/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedFunctorsDefs CohomologyConnection

universe v u

namespace RightDerivedDelta


section PerDegreeEffaceability

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end PerDegreeEffaceability


section DeltaFunctorData

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- Data exhibiting a cohomological δ-functor as the right derived δ-functor
of an additive functor `F : C ⥤ D`: the underlying δ-functor `δF`, an
identification `(δF)^n = F.rightDerived n` in each degree, and effaceability. -/
structure RightDerivedDeltaFunctorData (F : C ⥤ D) [F.Additive] where
  deltaFunctor : CohomDeltaFunctor C D
  degree_eq : ∀ n, deltaFunctor.T n = F.rightDerived n
  effaceable : deltaFunctor.IsEffaceable

/-- If a δ-functor agrees with the right derived functors in every degree
then it is effaceable, since the right derived functors are. -/
theorem effaceable_of_degree_eq
    (F : C ⥤ D) [F.Additive]
    (δF : CohomDeltaFunctor C D)
    (h : ∀ n, δF.T n = F.rightDerived n) :
    δF.IsEffaceable := by
  intro n X
  obtain ⟨I, i, hi, hI⟩ := rightDerived_effaceable_at F n X
  exact ⟨I, i, hi, h (n + 1) ▸ hI⟩

end DeltaFunctorData


section ExistenceTheorem

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end ExistenceTheorem


section NonSelfComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Comparison data between an effaceable Čech-type δ-functor `F₁` and an
arbitrary δ-functor `F₂`, packaged as a `CechToDerivedData` instance for
the universal property. -/
def nonSelfCechToDerivedData
    (F₁ F₂ : CohomDeltaFunctor C D) (hF₁ : F₁.IsEffaceable) :
    CechToDerivedData (C := C) (D := D) where
  cech := F₁
  derived := F₂
  cech_effaceable := hF₁

end NonSelfComparison


section ConcreteInstantiation

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end ConcreteInstantiation


section Summary

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end Summary

end RightDerivedDelta
