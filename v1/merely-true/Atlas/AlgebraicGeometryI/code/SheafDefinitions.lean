/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.unusedVariables false

namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- A presheaf on a category `J` with values in `C` is a contravariant functor
`Jᵒᵖ ⥤ C`. -/
abbrev Presheaf (J : Type*) [Category J] (C : Type*) [Category C] := Jᵒᵖ ⥤ C

/-- Pushforward of a presheaf along a covariant functor `u : J ⥤ K`: precompose
with `u.op` to obtain a presheaf on `J` from one on `K`. -/
def pushforwardPresheaf {J K : Type*} [Category J] [Category K]
    {C : Type*} [Category C] (u : J ⥤ K) (F : Presheaf K C) : Presheaf J C :=
  u.op ⋙ F

/-- The category of presheaves with values in an abelian category is abelian. -/
noncomputable instance presheafAbelian (C : Type*) [Category C] [Abelian C]
    (J : Type*) [Category J] : Abelian (J ⥤ C) := inferInstance

/-- An `O`-module is **locally free of rank `n`** if there is an open cover
`{U_i}` of `X` such that each restriction `M(U_i)` is a free `O(U_i)`-module of
rank `n`. -/
def IsLocallyFree {X : Type*} [TopologicalSpace X]
    (O : (Opens X)ᵒᵖ ⥤ CommRingCat)
    (M : ∀ (U : Opens X), Type*)
    [∀ U, AddCommGroup (M U)]
    [∀ U, Module (O.obj (Opposite.op U)) (M U)]
    (n : ℕ) : Prop :=
  ∃ (ι : Type*) (U : ι → Opens X),
    (⨆ i, U i = ⊤) ∧
    ∀ i, Module.Free (O.obj (Opposite.op (U i))) (M (U i)) ∧
      Module.finrank (O.obj (Opposite.op (U i))) (M (U i)) = n

/-- A globally free sheaf of rank `n` is locally free of rank `n`: take the
trivial one-element cover by the whole space. -/
theorem free_isLocallyFree {X : Type*} [TopologicalSpace X]
    (O : (Opens X)ᵒᵖ ⥤ CommRingCat)
    (M : ∀ (U : Opens X), Type*)
    [∀ U, AddCommGroup (M U)]
    [∀ U, Module (O.obj (Opposite.op U)) (M U)]
    (n : ℕ)
    [hfree : Module.Free (O.obj (Opposite.op ⊤)) (M ⊤)]
    (hrank : Module.finrank (O.obj (Opposite.op ⊤)) (M ⊤) = n) :
    IsLocallyFree O M n := by
  refine ⟨PUnit, fun _ => ⊤, ?_, ?_⟩
  · simp
  · intro i
    exact ⟨hfree, hrank⟩

end SheafDefinitions
