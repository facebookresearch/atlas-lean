/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.NormTrace

open CategoryTheory Opposite

noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

/-- The function field `K(X)` of an integral scheme `X` is a field
(Lec 6, Def 14 setting). -/
instance functionField_field (X : AlgebraicGeometry.Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

/-- The germ map from sections over a nonempty open of an integral scheme
into the function field `K(X)` is injective (Lec 6, Def 14). -/
theorem functionField_germ_injective (X : AlgebraicGeometry.Scheme) [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  AlgebraicGeometry.Scheme.germToFunctionField_injective X U

/-- For affine `Spec R` with `R` a domain, the function field is the
fraction field of `R` (Lec 6, Def 14 in the affine case). -/
instance functionField_isFractionRing_affine (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (AlgebraicGeometry.Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

/-- On an affine open `U` of an integral scheme `X`, the function field
`K(X)` is the fraction field of `Γ(X, U)` (Lec 6, Def 14). -/
theorem functionField_isFractionRing_of_affineOpen (X : AlgebraicGeometry.Scheme)
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU

/-- The function field of a domain `R`, defined as its fraction field
(Lec 6, Def 14, affine viewpoint). -/
abbrev functionField (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing R

/-- The function field of a domain is a field. -/
instance functionField.field (R : Type*) [CommRing R] [IsDomain R] :
    Field (functionField R) := inferInstance

/-- The domain `R` is an algebra over its function field. -/
instance functionField.algebra (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (functionField R) := inferInstance

/-- The function field of a domain is its fraction field. -/
instance functionField.isFractionRing (R : Type*) [CommRing R] [IsDomain R] :
    IsFractionRing R (functionField R) := inferInstance

/-- Degree of a dominant map `Spec A → Spec B` of integral affine schemes,
defined as the degree of the corresponding extension of function fields
(Lec 6, Def 15). -/
def degreeDominantMap (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)] :=
  Module.finrank (FractionRing B) (FractionRing A)


open Ideal in
/-- A prime `𝔭` of `B` is unramified in `A` if the number of primes of
`A` over `𝔭` equals the degree of the function field extension
(Lec 6, Def 16). -/
def Lec6IsUnramifiedOver (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)]
    (𝔭 : Ideal B) : Prop :=
  Set.ncard (Ideal.primesOver 𝔭 A) = Module.finrank (FractionRing B) (FractionRing A)

open Ideal in
/-- A prime `𝔭` of `B` is ramified in `A` if it is not unramified
(Lec 6, Def 16). -/
def Lec6IsRamifiedOver (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)]
    (𝔭 : Ideal B) : Prop :=
  ¬ Lec6IsUnramifiedOver A B 𝔭

/-- The ramification locus in `Spec A` of a finite free extension `A → B`,
defined as the zero locus of the discriminant
(Lec 6, Prop 7 setting). -/
def RamificationLocus (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus {Algebra.discr A (Module.Free.chooseBasis A B)}

/-- Lec 6, Prop 7: the ramification locus is closed in `Spec A`. -/
theorem ramificationLocus_isClosed (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] :
    IsClosed (RamificationLocus A B) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- If the discriminant of `A → B` is nonzero, then the ramification
locus is a proper subset of `Spec A` (Lec 6, Prop 7). -/
theorem ramificationLocus_ne_univ_of_discr_ne_zero
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B]
    (hd : Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0) :
    RamificationLocus A B ≠ Set.univ := by
  intro h
  have hmem := (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp h
  simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hmem
  rw [nilradical_eq_zero] at hmem
  exact hd hmem

/-- Helper for Lec 6, Prop 7: if the function field extension `K → L`
is finite separable, the discriminant of `A → B` is nonzero. -/
theorem discr_ne_zero_of_separable_functionField
    (A : Type*) (K : Type*) (B : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [Algebra.IsSeparable K L] [Module.Finite K L] :
    Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0 := by
  set b := Module.Free.chooseBasis A B

  set b' := b.localizationLocalization K (nonZeroDivisors A) L

  have hlocal : Algebra.discr K b' = (algebraMap A K) (Algebra.discr A b) :=
    Algebra.discr_localizationLocalization A (nonZeroDivisors A) L b

  have hne : Algebra.discr K b' ≠ 0 := Algebra.discr_not_zero_of_basis K b'

  rw [hlocal] at hne


  exact fun h => hne (by rw [h, map_zero])

/-- Lec 6, Prop 7: under separability of the function field extension,
the ramification locus is a proper subset. -/
theorem ramificationLocus_ne_univ_of_separable
    (A : Type*) (K : Type*) (B : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [Algebra.IsSeparable K L] [Module.Finite K L] :
    RamificationLocus A B ≠ Set.univ :=
  ramificationLocus_ne_univ_of_discr_ne_zero A B
    (discr_ne_zero_of_separable_functionField A K B L)

/-- Lec 6, Prop 7: the ramification locus is a proper closed subset of
`Spec A` when the function field extension is separable. -/
theorem ramificationLocus_properClosed_of_separable
    (A : Type*) (K : Type*) (B : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [Algebra.IsSeparable K L] [Module.Finite K L] :
    IsClosed (RamificationLocus A B) ∧
    RamificationLocus A B ≠ Set.univ :=
  ⟨ramificationLocus_isClosed A B, ramificationLocus_ne_univ_of_separable A K B L⟩

/-- The normalization of `R` in a finite extension of its fraction field
is integrally closed (Lec 6, normalization). -/
theorem normalization_is_normal
    {R : Type*} [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension K

/-- The structure map from a domain `B` into its integral closure in an
extension `L` of its fraction field is injective. -/
theorem normalization_map_injective
    (B : Type*) [CommRing B] [IsDomain B]
    (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
    (L : Type*) [Field L] [Algebra K L] [Algebra B L]
    [IsScalarTower B K L] :
    Function.Injective (algebraMap B (integralClosure B L)) := by
  haveI : IsScalarTower B (integralClosure B L) L :=
    IsScalarTower.subalgebra' B L L (integralClosure B L)
  exact algebraMap_injective_of_field_isFractionRing B (↥(integralClosure B L)) K L

/-- The integral closure of a noetherian, integrally closed domain `B`
in a finite separable extension of its fraction field is a finite
`B`-module. -/
theorem normalization_finite_module
    {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
    (L : Type*) [Field L] [Algebra K L] [Algebra B L]
    [IsScalarTower B K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    Module.Finite B (integralClosure B L) :=
  IsIntegralClosure.finite B K L (integralClosure B L)

/-- The integral closure of a noetherian, integrally closed domain in a
finite separable extension of its fraction field is noetherian. -/
theorem integral_closure_noetherian
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    IsNoetherianRing (integralClosure R L) :=
  integralClosure.isNoetherianRing (K := K) L

/-- The integral closure of a finite-type `k`-algebra `B` (assumed nice)
in a finite separable extension of its fraction field remains a finite-type
`k`-algebra. -/
theorem normalization_finiteType
    (k : Type*) [Field k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [IsIntegrallyClosed B] [IsNoetherianRing B]
    (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (L : Type*) [Field L] [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra k L] [IsScalarTower k B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.FiniteType k (integralClosure B L) := by
  haveI : Module.Finite B (integralClosure B L) :=
    normalization_finite_module K L
  exact Algebra.FiniteType.trans (‹Algebra.FiniteType k B›)
    (Module.Finite.finiteType (integralClosure B L))

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding is fully faithful. -/
def yoneda_fully_faithful (C : Type*) [Category C] :
    (coyoneda (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding is full. -/
theorem yoneda_full (C : Type*) [Category C] :
    (coyoneda (C := C)).Full :=
  (yoneda_fully_faithful C).full

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding is faithful. -/
theorem yoneda_faithful (C : Type*) [Category C] :
    (coyoneda (C := C)).Faithful :=
  (yoneda_fully_faithful C).faithful

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding reflects isomorphisms,
giving an iso `x ≅ y` from any iso of representable functors. -/
def yoneda_injective_on_objects (C : Type*) [Category C]
    {x y : Cᵒᵖ}
    (h : coyoneda.obj x ≅ coyoneda.obj y) :
    x ≅ y :=
  (yoneda_fully_faithful C).preimageIso h

/-- An affine variety `Spec R` is normal if `R` is an integrally closed
domain (Lec 6, normalization). -/
def IsNormalVariety (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsIntegrallyClosed R

/-- An integrally closed domain defines a normal affine variety. -/
theorem isNormalVariety_of_integrallyClosed
    (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalVariety R :=
  ‹IsIntegrallyClosed R›

/-- The normalization of a domain in a finite extension of its fraction
field is a normal variety (Lec 6, normalization). -/
theorem normalization_isNormalVariety
    {R : Type*} [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] :
    IsNormalVariety (integralClosure R L) :=
  normalization_is_normal K

/-- A local Dedekind domain that is not a field is a regular local ring,
i.e. a DVR (Lec 6, normalization in dimension one). -/
theorem dedekindDomain_localRing_isRegularLocalRing
    (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [IsLocalRing R] (h : ¬ IsField R) :
    IsRegularLocalRing R := by

  have : IsDiscreteValuationRing R := by
    have tfae := IsDiscreteValuationRing.TFAE R h
    exact (tfae.out 2 0).mp ‹IsDedekindDomain R›

  exact IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing R

/-- A Dedekind domain is integrally closed. -/
theorem dedekindDomain_isIntegrallyClosed
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] :
    IsIntegrallyClosed R := inferInstance

/-- A Dedekind domain defines a normal affine variety. -/
theorem dedekindDomain_isNormalVariety
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] :
    IsNormalVariety R :=
  dedekindDomain_isIntegrallyClosed R

end Lec6

end
