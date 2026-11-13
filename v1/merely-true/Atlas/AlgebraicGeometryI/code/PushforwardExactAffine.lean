/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace PushforwardExactAffine

/-- Restriction of scalars along a ring homomorphism preserves finite limits (it is a
right adjoint to extension of scalars). -/
noncomputable instance restrictScalars_preservesFiniteLimits
    {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} φ) := by
  have : PreservesLimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} φ) :=
    (ModuleCat.extendRestrictScalarsAdj φ).rightAdjoint_preservesLimits
  exact this.preservesFiniteLimits

/-- Restriction of scalars along a ring homomorphism preserves finite colimits (it is a
left adjoint to coextension of scalars). -/
noncomputable instance restrictScalars_preservesFiniteColimits
    {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} φ) := by
  have : PreservesColimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} φ) :=
    (ModuleCat.restrictCoextendScalarsAdj φ).leftAdjoint_preservesColimits
  exact this.preservesFiniteColimits

/-- Restriction of scalars is exact: it preserves both finite limits and finite
colimits. -/
theorem restrictScalars_exact
    {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} φ) ∧
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} φ) :=
  ⟨inferInstance, inferInstance⟩

/-- The pushforward of modules along a morphism of schemes preserves finite limits
(left-exactness of `f_*`). -/
noncomputable instance pushforward_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Scheme.Modules.pushforward f) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  infer_instance

end PushforwardExactAffine
