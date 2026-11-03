/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

/-- A primed variant of `LeftModuleCategoryStruct` used in the development of the module
functor formalism: it bundles the bifunctorial action data together with the associator and
left unitor isomorphisms, without the coherence axioms. -/
class LeftModuleCategoryStruct' (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  actObj : C → M → M
  actWhiskerLeft (X : C) {M₁ M₂ : M} (f : M₁ ⟶ M₂) : actObj X M₁ ⟶ actObj X M₂
  actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) : actObj X₁ N ⟶ actObj X₂ N
  actTensorHom {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actObj X₁ M₁ ⟶ actObj X₂ M₂ :=
    actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g
  actAssociator : ∀ (X Y : C) (N : M),
    actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  actLeftUnitor : ∀ (N : M), actObj (𝟙_ C) N ≅ N

namespace ModFun

export LeftModuleCategoryStruct' (actObj actWhiskerLeft actWhiskerRight actTensorHom
  actAssociator actLeftUnitor)

scoped infixr:70 " ⊗ᵐ " => LeftModuleCategoryStruct'.actObj

scoped infixr:81 " ◁ᵐ " => LeftModuleCategoryStruct'.actWhiskerLeft

scoped infixl:81 " ▷ᵐ " => LeftModuleCategoryStruct'.actWhiskerRight

scoped infixr:70 " ⊗ₘᵐ " => LeftModuleCategoryStruct'.actTensorHom

scoped notation "actμ_" => LeftModuleCategoryStruct'.actAssociator

scoped notation "actℓ_" => LeftModuleCategoryStruct'.actLeftUnitor

end ModFun

open ModFun

/-- A primed variant of `LeftModuleCategory`: extends `LeftModuleCategoryStruct'` with the
full set of coherence axioms (bifunctoriality, pentagon, triangle and unitor naturality)
for a left `C`-module category. -/
class LeftModuleCategory' (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] extends LeftModuleCategoryStruct' C M where
  actTensorHom_def {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actTensorHom f g = actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g := by
    rfl
  actId_tensorHom_id : ∀ (X : C) (N : M),
      actTensorHom (𝟙 X) (𝟙 N) = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actTensorHom_comp : ∀ {X₁ X₂ X₃ : C} {M₁ M₂ M₃ : M}
      (f₁ : X₁ ⟶ X₂) (g₁ : M₁ ⟶ M₂) (f₂ : X₂ ⟶ X₃) (g₂ : M₂ ⟶ M₃),
      actTensorHom f₁ g₁ ≫ actTensorHom f₂ g₂ = actTensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
    aesop_cat
  actWhiskerLeft_id : ∀ (X : C) (N : M), X ◁ᵐ 𝟙 N = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actId_whiskerRight : ∀ (X : C) (N : M), (𝟙 X) ▷ᵐ N = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actAssociator_naturality :
      ∀ {X₁ X₂ : C} {Y₁ Y₂ : C} {M₁ M₂ : M}
        (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : M₁ ⟶ M₂),
      actTensorHom (f ⊗ₘ g) h ≫ (actμ_ X₂ Y₂ M₂).hom =
        (actμ_ X₁ Y₁ M₁).hom ≫ actTensorHom f (actTensorHom g h) := by
    aesop_cat
  actLeftUnitor_naturality :
      ∀ {M₁ M₂ : M} (f : M₁ ⟶ M₂),
      (𝟙_ C) ◁ᵐ f ≫ (actℓ_ M₂).hom = (actℓ_ M₁).hom ≫ f := by
    aesop_cat
  actPentagon : ∀ (X Y Z : C) (N : M),
      (α_ X Y Z).hom ▷ᵐ N ≫ (actμ_ X (Y ⊗ Z) N).hom ≫ X ◁ᵐ (actμ_ Y Z N).hom =
        (actμ_ (X ⊗ Y) Z N).hom ≫ (actμ_ X Y (Z ⊗ᵐ N)).hom := by
    aesop_cat
  actTriangle : ∀ (X : C) (N : M),
      (actμ_ X (𝟙_ C) N).hom ≫ X ◁ᵐ (actℓ_ N).hom = (ρ_ X).hom ▷ᵐ N := by
    aesop_cat

attribute [reassoc] LeftModuleCategory'.actTensorHom_def
attribute [reassoc, simp] LeftModuleCategory'.actWhiskerLeft_id
attribute [reassoc, simp] LeftModuleCategory'.actId_whiskerRight
attribute [reassoc (attr := simp)] LeftModuleCategory'.actTensorHom_comp
attribute [reassoc] LeftModuleCategory'.actAssociator_naturality
attribute [reassoc] LeftModuleCategory'.actLeftUnitor_naturality
attribute [reassoc (attr := simp)] LeftModuleCategory'.actPentagon
attribute [reassoc (attr := simp)] LeftModuleCategory'.actTriangle

/-- A primed variant of `ModuleFunctor` between left `C`-module categories: an underlying
functor together with a natural isomorphism `F(X ⊗ N) ≅ X ⊗ F(N)` satisfying compatibility
with the associator and left unitor of the module structure. -/
structure ModuleFunctor'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory' C M₂] where
  toFunctor : M₁ ⥤ M₂
  strIso : ∀ (X : C) (N : M₁), toFunctor.obj (X ⊗ᵐ N) ≅ (X ⊗ᵐ toFunctor.obj N)
  strIso_natural : ∀ {X₁ X₂ : C} {N₁ N₂ : M₁} (f : X₁ ⟶ X₂) (g : N₁ ⟶ N₂),
      toFunctor.map (f ▷ᵐ N₁ ≫ X₂ ◁ᵐ g) ≫ (strIso X₂ N₂).hom =
        (strIso X₁ N₁).hom ≫ (f ▷ᵐ toFunctor.obj N₁ ≫ X₂ ◁ᵐ toFunctor.map g)
  strIso_assoc : ∀ (X Y : C) (N : M₁),
      toFunctor.map (actμ_ X Y N).hom ≫ (strIso X (Y ⊗ᵐ N)).hom ≫
        X ◁ᵐ (strIso Y N).hom =
      (strIso (X ⊗ Y) N).hom ≫ (actμ_ X Y (toFunctor.obj N)).hom
  strIso_unit : ∀ (N : M₁),
      toFunctor.map (actℓ_ N).hom = (strIso (𝟙_ C) N).hom ≫ (actℓ_ (toFunctor.obj N)).hom

attribute [reassoc] ModuleFunctor'.strIso_natural
attribute [reassoc (attr := simp)] ModuleFunctor'.strIso_assoc
attribute [reassoc (attr := simp)] ModuleFunctor'.strIso_unit

/-- A primed variant of `ModuleEquivalence`: a `ModuleFunctor'` whose underlying functor is
an equivalence of categories, giving an equivalence of left `C`-module categories. -/
structure ModuleEquivalence'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory' C M₂] extends
    ModuleFunctor' C M₁ M₂ where
  isEquivalence : toFunctor.IsEquivalence

end CategoryTheory
