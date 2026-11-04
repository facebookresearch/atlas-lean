/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

set_option maxHeartbeats 800000

noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- The scheme `Spec ℂ`, used as the base in the smooth-complex-curve setup of Lec 17. -/
def SpecC : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))

/-- A smooth compact complex curve: an integral scheme over `Spec ℂ` that is proper
and smooth of relative dimension `1`. -/
structure SmoothCompactComplexCurve where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isProper : IsProper structureMorphism
  isSmoothOfRelDim1 : SmoothOfRelativeDimension 1 structureMorphism

/-- Converts a complex period lattice into the Weierstrass cubic
`y² = 4x³ - g₂(L) x - g₃(L)`, with `aᵢ` coefficients adjusted to standard short form. -/
def periodPairToWeierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

/-- Two period pairs are homothetic if their lattices are scalar multiples of each
other by some nonzero complex `α`. -/
def LatticePairHomothetic (L₁ L₂ : PeriodPair) : Prop :=
  ∃ α : ℂ, α ≠ 0 ∧
    (∀ z : ℂ, z ∈ L₁.lattice ↔ ∃ w ∈ L₂.lattice, z = α * w)

/-- Period lattice data attached to a curve of genus `g`: a full-rank `ℤ`-submodule of
`ℂ^g`, representing the periods of holomorphic 1-forms. -/
structure PeriodLatticeData where
  genus : ℕ
  lattice : Submodule ℤ (Fin genus → ℂ)

/-- Two period lattice data are equivalent if there is a `ℂ`-linear isomorphism between
the ambient spaces carrying one lattice onto the other. -/
def PeriodLatticeData.Equivalent (D₁ D₂ : PeriodLatticeData) : Prop :=
  ∃ (φ : (Fin D₁.genus → ℂ) ≃ₗ[ℂ] (Fin D₂.genus → ℂ)),
    ∀ v : Fin D₁.genus → ℂ, v ∈ D₁.lattice ↔ φ v ∈ D₂.lattice

/-- Two smooth compact complex curves are isomorphic over `ℂ` if there is an
isomorphism of schemes compatible with their structure morphisms to `Spec ℂ`. -/
def SmoothCompactComplexCurve.IsIsomorphicOver (X₁ X₂ : SmoothCompactComplexCurve) : Prop :=
  ∃ (f : X₁.toScheme ⟶ X₂.toScheme), IsIso f ∧
    X₁.structureMorphism = f ≫ X₂.structureMorphism



/-- A (proper smooth) abelian group scheme over `Spec ℂ`: a proper smooth scheme over
`ℂ` with a chosen identity section. -/
structure AbelianGroupScheme where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmooth : Smooth structureMorphism
  identitySection : SpecC ⟶ toScheme
  identitySection_comp : identitySection ≫ structureMorphism = 𝟙 SpecC


/-- An irreducible complete curve over `k`: an integral Dedekind domain regarded as the
coordinate ring of a 1-dimensional smooth curve. -/
structure IrreducibleCompleteCurve (k : Type*) [Field k] : Type 1 where
  coordinateRing : Type
  [instCommRing : CommRing coordinateRing]
  [instIsDomain : IsDomain coordinateRing]
  [instIsDedekind : IsDedekindDomain coordinateRing]

attribute [instance] IrreducibleCompleteCurve.instCommRing
  IrreducibleCompleteCurve.instIsDomain IrreducibleCompleteCurve.instIsDedekind

/-- A morphism `X → Y` of irreducible complete curves, contravariantly described by a
ring homomorphism on coordinate rings `Y.coordinateRing → X.coordinateRing`. -/
structure CurveMorphism {k : Type*} [Field k]
    (X Y : IrreducibleCompleteCurve k) : Type where
  ringHom : Y.coordinateRing →+* X.coordinateRing

/-- Composition of curve morphisms, defined contravariantly via composition of the
underlying ring maps. -/
def CurveMorphism.comp {k : Type*} [Field k]
    {X Y Z : IrreducibleCompleteCurve k}
    (g : CurveMorphism Y Z) (f : CurveMorphism X Y) :
    CurveMorphism X Z where
  ringHom := f.ringHom.comp g.ringHom

/-- A curve morphism is constant iff the underlying ring map is not injective (i.e.
collapses some function on the target curve). -/
def CurveMorphism.IsConstant {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  ¬ Function.Injective f.ringHom

/-- A curve morphism is finite iff `X.coordinateRing` is module-finite over
`Y.coordinateRing` via `f.ringHom`. -/
def CurveMorphism.IsFinite {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  letI : Algebra Y.coordinateRing X.coordinateRing := f.ringHom.toAlgebra
  Module.Finite Y.coordinateRing X.coordinateRing

/-- A curve morphism is an isomorphism iff its underlying ring map is bijective. -/
def CurveMorphism.IsIsomorphism {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Bijective f.ringHom

/-- A curve morphism is birational iff its ring map is injective and every element of
`X.coordinateRing` is a fraction of elements pulled back from `Y.coordinateRing`. -/
def CurveMorphism.IsBirational {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Injective f.ringHom ∧
  ∀ a : X.coordinateRing, ∃ (b : Y.coordinateRing) (s : Y.coordinateRing),
    s ≠ 0 ∧ f.ringHom s * a = f.ringHom b

/-- A curve is normal iff its coordinate ring is integrally closed in its field of
fractions. -/
def IrreducibleCompleteCurve.IsNormal {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Prop :=
  IsIntegrallyClosed X.coordinateRing

/-- The Picard group `Pic⁰(X)` of a curve, modeled as the ideal class group of its
Dedekind coordinate ring. -/
def IrreducibleCompleteCurve.Pic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Type :=
  ClassGroup X.coordinateRing

/-- `Pic⁰(X)` inherits a commutative group structure from the class group. -/
instance instCommGroupPic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : CommGroup X.Pic0Group := by
  unfold IrreducibleCompleteCurve.Pic0Group; infer_instance






/-- The affine points of an elliptic Weierstrass curve form an abelian group. -/
instance elliptic_curve_addCommGroup
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    AddCommGroup W.Point :=
  inferInstance



end Lec17AbelJacobi
