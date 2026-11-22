/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Category

set_option maxHeartbeats 800000

open CategoryTheory

universe v v₁ u u₁

/-- `Y` is a subquotient of `Z` when there is some object `A` mapping monomorphically into `Z`
and epimorphically onto `Y`. -/
def IsSubquotientOf {C : Type u} [Category.{v} C] (Y Z : C) : Prop :=
  ∃ (A : C) (m : A ⟶ Z) (e : A ⟶ Y), Mono m ∧ Epi e

/-- A functor is a surjective tensor functor when every object of the target is a subquotient of
some `F.obj X`. -/
class IsSurjectiveTensorFunctor
    {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) : Prop where
  surjective : ∀ (Y : D), ∃ (X : C), IsSubquotientOf Y (F.obj X)
