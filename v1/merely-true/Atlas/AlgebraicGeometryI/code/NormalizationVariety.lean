/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

set_option maxHeartbeats 400000

noncomputable section

namespace NormalizationVariety

/-- The integral closure of a normal finitely-generated k-algebra A in a finite separable
field extension E/K of its fraction field is a finite A-module: the normalization map
Y → X is finite (Proposition 28, Lecture 17). -/
theorem normalization_is_finite
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra A E] [IsScalarTower A K E]
    [Algebra.IsSeparable K E] :
    Module.Finite A (integralClosure A E) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsScalarTower A (↥(integralClosure A E)) E :=
    IsScalarTower.subalgebra' A E E (integralClosure A E)
  exact IsIntegralClosure.finite A K E (integralClosure A E)

/-- The normalization is itself a finitely-generated k-algebra: composing the finite
A-module structure with finite-type A/k gives finite-type Y/k. -/
theorem normalization_finiteType
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra A E] [IsScalarTower A K E]
    [Algebra k E] [IsScalarTower k A E]
    [Algebra.IsSeparable K E] :
    Algebra.FiniteType k (integralClosure A E) := by
  haveI : Module.Finite A (integralClosure A E) :=
    normalization_is_finite k A K E
  exact Algebra.FiniteType.trans (‹Algebra.FiniteType k A›)
    (Module.Finite.finiteType (integralClosure A E))

/-- The integral closure of A in a finite extension of its fraction field is
integrally closed; that is, the normalization variety is itself normal. -/
theorem normalization_is_normal
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra A E] [IsScalarTower A K E] :
    IsIntegrallyClosed (integralClosure A E) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension K

/-- The structure map A → (integral closure of A in E) is injective, so the
normalization map Y → X is dominant. -/
theorem normalization_map_injective
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] :
    Function.Injective (algebraMap A (integralClosure A E)) := by
  haveI : IsScalarTower A (integralClosure A E) E :=
    IsScalarTower.subalgebra' A E E (integralClosure A E)
  exact algebraMap_injective_of_field_isFractionRing A (↥(integralClosure A E)) K E

/-- Existence of the normalization variety (Proposition 28, Lecture 17): there exists
a normal variety Y with a finite dominant map Y → X whose coordinate ring is the
integral closure of A in E. -/
theorem normalization_existence
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra A E] [IsScalarTower A K E]
    [Algebra k E] [IsScalarTower k A E]
    [Algebra.IsSeparable K E] :

    Module.Finite A (integralClosure A E) ∧

    Algebra.FiniteType k (integralClosure A E) ∧

    IsIntegrallyClosed (integralClosure A E) ∧

    Function.Injective (algebraMap A (integralClosure A E)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact normalization_is_finite k A K E
  · exact normalization_finiteType k A K E
  · exact normalization_is_normal A K E
  · exact normalization_map_injective A K E

open AlgebraicGeometry CategoryTheory in
/-- The normalization factorization: any morphism f : X → Y factors as
X → Norm(Y) → Y through the normalization. -/
theorem normalization_factorization_scheme
    {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    f.toNormalization ≫ f.fromNormalization = f :=
  f.toNormalization_fromNormalization

open AlgebraicGeometry CategoryTheory in
/-- The structural map Norm(Y) → Y from the normalization is an integral morphism. -/
theorem normalization_fromNormalization_integral
    {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom f.fromNormalization :=
  inferInstance

open AlgebraicGeometry CategoryTheory in
/-- The map X → Norm(Y) into the normalization is dominant. -/
theorem normalization_toNormalization_dominant
    {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsDominant f.toNormalization :=
  inferInstance

open AlgebraicGeometry CategoryTheory in
/-- Local description: on an affine open U ⊆ Y, the sections of the normalization
over f⁻¹(U) form the integral closure of Γ(Y,U) in Γ(X, f⁻¹(U)). -/
theorem normalization_sections_isIntegralClosure
    {X Y : Scheme} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Nonempty (Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :=
  ⟨f.normalizationObjIso hU⟩

end NormalizationVariety

end
