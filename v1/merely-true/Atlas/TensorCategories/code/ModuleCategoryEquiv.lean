/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Atlas.TensorCategories.code.TensorCategoryDef

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory TensorCategories

universe v₁ v₂ u₁ u₂

/-- Bundled data of an exact `C`-module category structure on `M`: the action bifunctor,
the associativity and unit isomorphisms, naturality, pentagon and triangle relations,
linearity, and exactness (preservation of monos and epis) of the action. -/
structure ExactModuleCategoryData
    (k : Type*) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
      [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
      [MultitensorCategory k C]
    (M : Type u₂) [Category.{v₂} M] [Preadditive M] [Linear k M] [Abelian M]
      [LocallyFiniteCategory k M] where
  actObj : C → M → M
  actWhiskerLeft : (X : C) → {N₁ N₂ : M} → (N₁ ⟶ N₂) → (actObj X N₁ ⟶ actObj X N₂)
  actWhiskerRight : {X₁ X₂ : C} → (X₁ ⟶ X₂) → (N : M) → (actObj X₁ N ⟶ actObj X₂ N)
  actAssociator : ∀ (X Y : C) (N : M), actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  actLeftUnitor : ∀ (N : M), actObj (𝟙_ C) N ≅ N
  actWhiskerLeft_id : ∀ (X : C) (N : M), actWhiskerLeft X (𝟙 N) = 𝟙 (actObj X N)
  actWhiskerLeft_comp : ∀ (X : C) {N₁ N₂ N₃ : M} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃),
    actWhiskerLeft X (f ≫ g) = actWhiskerLeft X f ≫ actWhiskerLeft X g
  actLeftUnitor_naturality : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂),
    actWhiskerLeft (𝟙_ C) f ≫ (actLeftUnitor N₂).hom = (actLeftUnitor N₁).hom ≫ f
  actPentagon : ∀ (X Y Z : C) (N : M),
    (actAssociator (X ⊗ Y) Z N).hom ≫ (actAssociator X Y (actObj Z N)).hom =
      actWhiskerRight (α_ X Y Z).hom N ≫ (actAssociator X (Y ⊗ Z) N).hom ≫
        actWhiskerLeft X (actAssociator Y Z N).hom
  actTriangle : ∀ (X : C) (N : M),
    (actAssociator X (𝟙_ C) N).hom ≫ actWhiskerLeft X (actLeftUnitor N).hom =
      actWhiskerRight (ρ_ X).hom N
  actWhiskerLeft_smul : ∀ (X : C) {N₁ N₂ : M} (r : k) (f : N₁ ⟶ N₂),
    actWhiskerLeft X (r • f) = r • actWhiskerLeft X f
  actWhiskerRight_smul : ∀ {X₁ X₂ : C} (r : k) (f : X₁ ⟶ X₂) (N : M),
    actWhiskerRight (r • f) N = r • actWhiskerRight f N
  actWhiskerLeft_preserves_mono : ∀ (X : C) {N₁ N₂ : M} (g : N₁ ⟶ N₂) [Mono g],
    Mono (actWhiskerLeft X g)
  actWhiskerLeft_preserves_epi : ∀ (X : C) {N₁ N₂ : M} (g : N₁ ⟶ N₂) [Epi g],
    Epi (actWhiskerLeft X g)
  actWhiskerRight_preserves_mono : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) [Mono f] (N : M),
    Mono (actWhiskerRight f N)
  actWhiskerRight_preserves_epi : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) [Epi f] (N : M),
    Epi (actWhiskerRight f N)

/-- Bundled data of an exact monoidal functor `C ⥤ (M ⥤ M)` from `C` into the category of
endofunctors of `M`, with the components and natural transformations being exact. -/
structure ExactMonoidalFunctorToEndL
    (k : Type*) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
      [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
      [MultitensorCategory k C]
    (M : Type u₂) [Category.{v₂} M] [Preadditive M] [Linear k M] [Abelian M]
      [LocallyFiniteCategory k M] where
  toFunctor : C ⥤ (M ⥤ M)
  component_preserves_mono : ∀ (X : C) {N₁ N₂ : M} (f : N₁ ⟶ N₂) [Mono f],
    Mono ((toFunctor.obj X).map f)
  component_preserves_epi : ∀ (X : C) {N₁ N₂ : M} (f : N₁ ⟶ N₂) [Epi f],
    Epi ((toFunctor.obj X).map f)
  unitIso : toFunctor.obj (𝟙_ C) ≅ 𝟭 M
  tensorIso : ∀ (X Y : C), toFunctor.obj (X ⊗ Y) ≅ toFunctor.obj Y ⋙ toFunctor.obj X
  pentagon : ∀ (X Y Z : C) (N : M),
    (toFunctor.map (α_ X Y Z).hom).app N ≫
      (tensorIso X (Y ⊗ Z)).hom.app N ≫
      (toFunctor.obj X).map ((tensorIso Y Z).hom.app N) =
    (tensorIso (X ⊗ Y) Z).hom.app N ≫ (tensorIso X Y).hom.app ((toFunctor.obj Z).obj N)
  triangle : ∀ (X : C) (N : M),
    (tensorIso X (𝟙_ C)).hom.app N ≫ (toFunctor.obj X).map (unitIso.hom.app N) =
      (toFunctor.map (ρ_ X).hom).app N
  functor_preserves_mono : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) [Mono f] (N : M),
    Mono ((toFunctor.map f).app N)
  functor_preserves_epi : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) [Epi f] (N : M),
    Epi ((toFunctor.map f).app N)




