/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SheafCohDerived
import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits
open SheafCohomology CohomologyP1 DerivedFunctorsDefs

namespace CohomologyConnection


section SerreVanishing

variable (A : Type*) [CommRing A] (f g : A)

end SerreVanishing


section CechP1

variable (k : Type) [Field k]

end CechP1


section DerivedSide

universe w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

end DerivedSide


section BridgingStructures

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Bundle of data comparing a Čech-style δ-functor to a derived-functor δ-functor, with the
Čech side being effaceable. -/
structure CechToDerivedData where
  cech : CohomDeltaFunctor C D
  derived : CohomDeltaFunctor C D
  cech_effaceable : cech.IsEffaceable

/-- Two morphisms between the Čech and derived δ-functors agreeing in degree zero agree in
every degree, by effaceability of the source. -/
theorem CechToDerivedData.morphisms_unique
    (data : CechToDerivedData (C := C) (D := D))
    (m₁ m₂ : data.cech.Morphism data.derived)
    (h₀ : m₁.η 0 = m₂.η 0) :
    ∀ n, m₁.η n = m₂.η n :=
  effaceable_morphism_unique data.cech data.derived data.cech_effaceable m₁ m₂ h₀

/-- Extension of `CechToDerivedData` packaging a chosen comparison morphism from the Čech
δ-functor to the derived δ-functor. -/
structure CechDerivedComparison extends CechToDerivedData (C := C) (D := D) where
  comparison : toCechToDerivedData.cech.Morphism toCechToDerivedData.derived

/-- The comparison morphism in a `CechDerivedComparison` is uniquely determined by its degree
zero component. -/
theorem CechDerivedComparison.comparison_unique
    (comp : CechDerivedComparison (C := C) (D := D))
    (m : comp.cech.Morphism comp.derived)
    (h₀ : m.η 0 = comp.comparison.η 0) :
    ∀ n, m.η n = comp.comparison.η n :=
  comp.toCechToDerivedData.morphisms_unique m comp.comparison h₀

/-- Extension of `CechToDerivedData` packaging both directions of an isomorphism between the
Čech and derived δ-functors, plus effaceability of the derived side. -/
structure CechDerivedIsomorphism extends CechToDerivedData (C := C) (D := D) where
  forward : toCechToDerivedData.cech.Morphism toCechToDerivedData.derived
  backward : toCechToDerivedData.derived.Morphism toCechToDerivedData.cech
  derived_effaceable : toCechToDerivedData.derived.IsEffaceable

/-- The forward isomorphism is uniquely determined by its degree zero component. -/
theorem CechDerivedIsomorphism.forward_unique
    (iso : CechDerivedIsomorphism (C := C) (D := D))
    (m : iso.cech.Morphism iso.derived)
    (h₀ : m.η 0 = iso.forward.η 0) :
    ∀ n, m.η n = iso.forward.η n :=
  iso.toCechToDerivedData.morphisms_unique m iso.forward h₀

/-- The backward isomorphism is uniquely determined by its degree zero component. -/
theorem CechDerivedIsomorphism.backward_unique
    (iso : CechDerivedIsomorphism (C := C) (D := D))
    (m : iso.derived.Morphism iso.cech)
    (h₀ : m.η 0 = iso.backward.η 0) :
    ∀ n, m.η n = iso.backward.η n :=
  effaceable_morphism_unique iso.derived iso.cech iso.derived_effaceable m iso.backward h₀

end BridgingStructures


section FullConnection

variable (k : Type) [Field k]

end FullConnection


section DerivedFacts

universe v₂ u₂

variable {C : Type u₂} [Category.{v₂} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

end DerivedFacts

end CohomologyConnection
