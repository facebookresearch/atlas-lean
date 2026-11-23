/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.MacLaneCoherence
import Atlas.TensorCategories.code.MacLaneStrictness
import Atlas.TensorCategories.code.InvertibleObjects
import Atlas.TensorCategories.code.TensorCategoryDef
import Atlas.TensorCategories.code.TensorExact
import Atlas.TensorCategories.code.GrothendieckRing
import Atlas.TensorCategories.code.FiniteAbelianCategoryDef

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

/-- Reference abbreviation for the definition of an invertible object in a
monoidal category. -/
abbrev IsInvertibleObject_def := @IsInvertibleObject

/-- The tensor inverse of an invertible object is itself invertible. -/
noncomputable def invertibleObject_inverse_invertible {C : Type*} [Category C] [MonoidalCategory C]
    (X : C) [h : IsInvertibleObject X] : IsInvertibleObject h.tensorInverse :=
  IsInvertibleObject.inverseInvertible X

/-- For an invertible object `X` in a rigid monoidal category, the canonical left
and right duals are isomorphic. -/
noncomputable def invertibleObject_leftDual_iso_rightDual
    {C : Type*} [Category C] [MonoidalCategory C] [RigidCategory C]
    (X : C) [HasRightDual X] [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))] :
    HasLeftDual.leftDual X ≅ Xᘁ :=
  leftDualIsoRightDual_of_invertible X

/-- The tensor product of two invertible objects in a rigid monoidal category is
again invertible. -/
noncomputable def invertibleObject_tensor
    {C : Type*} [Category C] [MonoidalCategory C] [RigidCategory C]
    (X Y : C) [hX : IsInvertibleObject X] [hY : IsInvertibleObject Y] :
    IsInvertibleObject (X ⊗ Y) :=
  tensor_invertible X Y

/-- Reference abbreviation for the definition of a finite abelian category. -/
abbrev IsFiniteAbelianCategory_def := @IsFiniteAbelianCategory

/-- The ring homomorphism between Grothendieck rings induced by a homomorphism of
fusion rings. -/
def grothendieckRing_induced_hom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRing.FusionRingHom R S) :
    FusionRing.GrRingOf R →+* FusionRing.GrRingOf S :=
  φ.inducedRingHom
