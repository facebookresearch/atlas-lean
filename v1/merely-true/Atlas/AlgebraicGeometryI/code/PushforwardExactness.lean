/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Grp.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

universe u v

namespace PushforwardExactness

/-- Affine pushforward (restriction of scalars) preserves finite limits. -/
noncomputable instance pushforward_affine_preservesFiniteLimits
    {R S : Type v} [CommRing R] [CommRing S] (phi : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} phi) := by
  have : PreservesLimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} phi) :=
    (ModuleCat.extendRestrictScalarsAdj phi).rightAdjoint_preservesLimits
  exact this.preservesFiniteLimits

/-- Affine pushforward (restriction of scalars) preserves finite colimits. -/
noncomputable instance pushforward_affine_preservesFiniteColimits
    {R S : Type v} [CommRing R] [CommRing S] (phi : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} phi) := by
  have : PreservesColimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} phi) :=
    (ModuleCat.restrictCoextendScalarsAdj phi).leftAdjoint_preservesColimits
  exact this.preservesFiniteColimits

/-- Exactness of affine pushforward: it preserves both finite limits and finite
colimits. -/
theorem pushforward_affine_exact
    {R S : Type v} [CommRing R] [CommRing S] (phi : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} phi) ∧
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} phi) :=
  ⟨inferInstance, inferInstance⟩

/-- The pushforward functor on sheaves of abelian groups along a morphism of schemes. -/
noncomputable def schemePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf AddCommGrpCat.{u} (Scheme.forgetToTop.obj X) ⥤
    Sheaf AddCommGrpCat.{u} (Scheme.forgetToTop.obj Y) :=
  Sheaf.pushforward AddCommGrpCat.{u} (Scheme.forgetToTop.map f)

/-- The pullback–pushforward adjunction `f⁻¹ ⊣ f_*` for sheaves of abelian groups on
the underlying topological spaces of schemes. -/
noncomputable def schemePullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.pullback AddCommGrpCat.{u} (Scheme.forgetToTop.map f) ⊣ schemePushforward f :=
  Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Scheme.forgetToTop.map f)

/-- Sheaf-level pushforward is left exact: as a right adjoint, it preserves finite
limits. -/
noncomputable instance pushforward_leftExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (schemePushforward f) := by
  have := (schemePullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  infer_instance

end PushforwardExactness
