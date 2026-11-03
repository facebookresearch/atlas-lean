/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Endomorphism

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

section EndRingStructure

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The `k`-action on `End P` commutes with right-composition by an endomorphism, so
`End P` carries a scalar tower over `k` with itself as the inner ring. -/
instance endScalarTower (P : C) : IsScalarTower k (End P) (End P) where
  smul_assoc r a b := by
    show b ≫ (r • a) = r • (b ≫ a)
    exact Linear.comp_smul P P P b r a

/-- A finite-dimensional endomorphism algebra over a field is Artinian as a ring,
obtained by transferring the Artinian property from `k`-modules. -/
theorem endRing_isArtinian {P : C} [FiniteDimensional k (End P)] :
    IsArtinianRing (End P) :=
  isArtinian_of_tower k (inferInstance : IsArtinian k (End P))

end EndRingStructure

section PostCompMap

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {P : C}

/-- Post-composition by a fixed endomorphism `g : End P`, viewed as a `k`-linear
endomorphism of the `k`-vector space `End P`. -/
def postCompEndMap (g : End P) : Module.End k (End P) where
  toFun h := h ≫ g
  map_add' h₁ h₂ := Preadditive.add_comp P P P h₁ h₂ g
  map_smul' r h := by
    simp only [RingHom.id_apply]
    exact Linear.smul_comp _ _ _ r h g

end PostCompMap

/-- A `k`-linear abelian category satisfies the Fitting property if every indecomposable
object has a local endomorphism ring. This holds in finite abelian categories. -/
class FiniteAbelianCategory.HasLocalEndOfIndecomposable
    (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C] [Linear k C] : Prop where
  isLocalRing_end_of_indecomposable :
    ∀ (P : C), Indecomposable P → IsLocalRing (End P)

section ProjectiveCoversOfSimples

end ProjectiveCoversOfSimples

end CategoryTheory
