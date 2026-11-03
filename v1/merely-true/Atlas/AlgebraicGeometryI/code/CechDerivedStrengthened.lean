/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Composition of morphisms of cohomological delta functors. -/
def CohomDeltaFunctor.compMorphism {F G H : CohomDeltaFunctor C D}
    (m₁ : F.Morphism G) (m₂ : G.Morphism H) : F.Morphism H where
  η n := m₁.η n ≫ m₂.η n
  comm_δ n S hS := by
    simp only [NatTrans.comp_app]


    rw [Category.assoc, m₂.comm_δ n S hS, ← Category.assoc,
        ← Category.assoc, m₁.comm_δ n S hS, Category.assoc]

/-- The `n`-th component of a composition of delta-functor morphisms is the composition of the
components. -/
@[simp]
theorem CohomDeltaFunctor.compMorphism_η {F G H : CohomDeltaFunctor C D}
    (m₁ : F.Morphism G) (m₂ : G.Morphism H) (n : ℕ) :
    (CohomDeltaFunctor.compMorphism m₁ m₂).η n = m₁.η n ≫ m₂.η n := rfl

end DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

end DerivedFunctorsDefs


namespace CechDerivedComparison

universe v₂ u₂

variable {C : Type u₂} [Category.{v₂} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

open DerivedFunctorsDefs

/-- An endomorphism of an effaceable delta functor that is the identity in degree zero is the
identity in every degree, by the uniqueness of effaceable extensions. -/
theorem roundtrip_eq_id_of_effaceable (F : CohomDeltaFunctor C D)
    (hF : F.IsEffaceable) (m : F.Morphism F)
    (h₀ : m.η 0 = 𝟙 (F.T 0)) :
    ∀ n, m.η n = 𝟙 (F.T n) := by
  have := effaceable_morphism_unique F F hF m F.idMorphism
    (by rw [h₀]; rfl)
  intro n
  rw [this n]
  rfl

end CechDerivedComparison


namespace CechDerivedIsomorphismProof

universe v₃ u₃

variable {C : Type u₃} [Category.{v₃} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

open DerivedFunctorsDefs CohomologyConnection

/-- Data witnessing a comparison between Čech and derived-functor cohomology as delta functors,
with mutually inverse morphisms in degree zero and effaceability hypotheses to extend the inverse
to all degrees. -/
structure CechDerivedComparisonData where
  cech : CohomDeltaFunctor C D
  derived : CohomDeltaFunctor C D
  cech_effaceable : cech.IsEffaceable
  derived_effaceable : derived.IsEffaceable
  forward : cech.Morphism derived
  backward : derived.Morphism cech
  forward_backward_zero : forward.η 0 ≫ backward.η 0 = 𝟙 (cech.T 0)
  backward_forward_zero : backward.η 0 ≫ forward.η 0 = 𝟙 (derived.T 0)

variable (data : CechDerivedComparisonData (C := C) (D := D))

/-- The composition `forward ∘ backward` is the identity in every degree. -/
theorem CechDerivedComparisonData.forward_backward_eq_id (n : ℕ) :
    data.forward.η n ≫ data.backward.η n = 𝟙 (data.cech.T n) := by
  let comp := CohomDeltaFunctor.compMorphism data.forward data.backward
  have h₀ : comp.η 0 = 𝟙 (data.cech.T 0) := data.forward_backward_zero
  have := CechDerivedComparison.roundtrip_eq_id_of_effaceable
    data.cech data.cech_effaceable comp h₀
  exact this n

/-- The composition `backward ∘ forward` is the identity in every degree. -/
theorem CechDerivedComparisonData.backward_forward_eq_id (n : ℕ) :
    data.backward.η n ≫ data.forward.η n = 𝟙 (data.derived.T n) := by
  let comp := CohomDeltaFunctor.compMorphism data.backward data.forward
  have h₀ : comp.η 0 = 𝟙 (data.derived.T 0) := data.backward_forward_zero
  have := CechDerivedComparison.roundtrip_eq_id_of_effaceable
    data.derived data.derived_effaceable comp h₀
  exact this n

/-- The forward comparison map is an isomorphism in every degree. -/
theorem CechDerivedComparisonData.forward_isIso (n : ℕ) :
    IsIso (data.forward.η n) := by
  refine ⟨⟨data.backward.η n, ?_, ?_⟩⟩
  ·
    have h := data.forward_backward_eq_id n


    exact h
  ·
    exact data.backward_forward_eq_id n

/-- The backward comparison map is an isomorphism in every degree. -/
theorem CechDerivedComparisonData.backward_isIso (n : ℕ) :
    IsIso (data.backward.η n) := by
  refine ⟨⟨data.forward.η n, ?_, ?_⟩⟩
  · exact data.backward_forward_eq_id n
  · exact data.forward_backward_eq_id n

/-- Uniqueness: any morphism `cech → derived` agreeing with `forward` in degree zero agrees with
it in every degree. -/
theorem CechDerivedComparisonData.comparison_unique
    (m : data.cech.Morphism data.derived) (h₀ : m.η 0 = data.forward.η 0) :
    ∀ n, m.η n = data.forward.η n :=
  effaceable_morphism_unique data.cech data.derived data.cech_effaceable
    m data.forward h₀

/-- Uniqueness of the inverse: any morphism `derived → cech` agreeing with `backward` in degree
zero agrees with it in every degree. -/
theorem CechDerivedComparisonData.inverse_unique
    (m : data.derived.Morphism data.cech) (h₀ : m.η 0 = data.backward.η 0) :
    ∀ n, m.η n = data.backward.η n :=
  effaceable_morphism_unique data.derived data.cech data.derived_effaceable
    m data.backward h₀


/-- A `CechDerivedIsomorphism` enriched with explicit degree-zero invertibility witnesses,
suitable for promoting the comparison to all degrees. -/
structure CechDerivedFullComparison extends
    CechDerivedIsomorphism (C := C) (D := D) where
  forward_backward_zero :
    toCechDerivedIsomorphism.forward.η 0 ≫
    toCechDerivedIsomorphism.backward.η 0 =
    𝟙 (toCechDerivedIsomorphism.cech.T 0)
  backward_forward_zero :
    toCechDerivedIsomorphism.backward.η 0 ≫
    toCechDerivedIsomorphism.forward.η 0 =
    𝟙 (toCechDerivedIsomorphism.derived.T 0)

/-- Repackage a `CechDerivedFullComparison` as `CechDerivedComparisonData`. -/
def CechDerivedFullComparison.toComparisonData
    (comp : CechDerivedFullComparison (C := C) (D := D)) :
    CechDerivedComparisonData (C := C) (D := D) where
  cech := comp.cech
  derived := comp.derived
  cech_effaceable := comp.cech_effaceable
  derived_effaceable := comp.derived_effaceable
  forward := comp.forward
  backward := comp.backward
  forward_backward_zero := comp.forward_backward_zero
  backward_forward_zero := comp.backward_forward_zero

/-- The forward comparison map from a `CechDerivedFullComparison` is an isomorphism in every
degree. -/
theorem CechDerivedFullComparison.forward_isIso
    (comp : CechDerivedFullComparison (C := C) (D := D)) (n : ℕ) :
    IsIso (comp.forward.η n) :=
  comp.toComparisonData.forward_isIso n

end CechDerivedIsomorphismProof
