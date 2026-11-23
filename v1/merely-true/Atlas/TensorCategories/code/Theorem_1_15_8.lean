/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple

open CategoryTheory MonoidalCategory Limits

universe u v

/-- Theorem 1.15.8: In a ring category with right duals, if the unit object `𝟙_ C` is
indecomposable then it is simple. This is the part (i) of the theorem from
Etingof–Gelaki–Nikshych–Ostrik, stating semisimplicity of the unit in the indecomposable case. -/
theorem Theorem_1_15_8_unit_is_simple
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Abelian C] [RightRigidCategory C] [LeftRigidCategory C]
    [MonoidalPreadditive C] [TensorCategories.MonoidalBiexact C]
    [IsArtinianRing (End (𝟙_ C))] [IsArtinianObject (𝟙_ C)]
    (hIndecomp : Indecomposable (𝟙_ C)) :
    Simple (𝟙_ C) :=
  TensorCategories.unitIsSimple C hIndecomp
