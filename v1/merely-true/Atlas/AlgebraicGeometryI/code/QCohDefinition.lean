/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `F` is conservative if it reflects isomorphisms: whenever
`F.map g` is an isomorphism, so is `g`. -/
def IsConservative (F : C ⥤ D) : Prop :=
  ∀ ⦃A B : C⦄ (g : A ⟶ B), IsIso (F.map g) → IsIso g

/-- The plain `Prop` notion `IsConservative` agrees with the type-class
`ReflectsIsomorphisms` from mathlib. -/
theorem isConservative_iff_reflectsIsomorphisms (F : C ⥤ D) :
    IsConservative F ↔ F.ReflectsIsomorphisms where
  mp h := ⟨fun f => h f ‹_›⟩
  mpr := fun ⟨inst⟩ _ _ g hiso => @inst _ _ g hiso
