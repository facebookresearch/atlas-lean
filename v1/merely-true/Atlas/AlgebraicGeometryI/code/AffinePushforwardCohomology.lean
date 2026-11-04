/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.Abelian

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

/-- The global sections functor `Γ(X, -) : X.Modules ⥤ Ab` sending a sheaf of `O_X`-modules to
its abelian group of global sections. -/
def Scheme.Modules.globalSectionsFunctor (X : Scheme.{u}) :
    X.Modules ⥤ Ab where
  obj F := Γ(F, ⊤)
  map φ := Scheme.Modules.Hom.app φ ⊤
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Γ(X, -)` is an additive functor. -/
instance Scheme.Modules.globalSectionsFunctor_additive
    (X : Scheme.{u}) : (Scheme.Modules.globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

/-- Naturally isomorphic additive functors have naturally isomorphic right derived functors:
if `F ≅ G` then `RⁿF ≅ RⁿG` for every `n`. -/
def rightDerivedFunctorIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    (τ : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived τ.hom n
  inv := NatTrans.rightDerived τ.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, τ.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, τ.inv_hom_id, NatTrans.rightDerived_id]






end
