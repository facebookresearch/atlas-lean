/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRingCategorical

open CategoryTheory MonoidalCategory

universe v u

/-- Proposition 1.45.2: If `C` is a ring category with right duals (here, an abelian
rigid monoidal `κ`-linear category with the fusion data needed to form its Grothendieck
ring), then `Gr(C)` is a transitive unital `ℤ₊`-ring. -/
theorem Proposition_1_45_2
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).IsTransitive :=
  CategoricalFusionData.toFusionRing.isTransitive

/-- The fusion ring (Grothendieck ring) underlying the categorical fusion data on `C`,
provided as a packaged form of Proposition 1.45.2. -/
def Proposition_1_45_2_fusionRing
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    FusionRing cfd.ι :=
  CategoricalFusionData.toFusionRing

/-- The ring instance on the Grothendieck ring of the categorical fusion data on `C`,
provided as part of Proposition 1.45.2. -/
def Proposition_1_45_2_ring_instance
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    Ring (FusionRing.GrRingOf (CategoricalFusionData.toFusionRing (κ := κ) (C := C))) :=
  FusionRing.GrRingOf.instRing
