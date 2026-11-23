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

/-- Definition 2.1.1 (EGNO): A left module category over a monoidal category `C` is a category
`M` equipped with a bifunctorial action `⊗ : C × M → M`, an associator natural isomorphism
`(X ⊗ Y) ⊗ N ≅ X ⊗ (Y ⊗ N)`, and a unit functor `𝟙_C ⊗ -` that is an equivalence, satisfying
the pentagon coherence axiom. -/
class Definition_2_1_1_LeftModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  actObj : C → M → M
  actWhiskerLeft (X : C) {M₁ M₂ : M} (f : M₁ ⟶ M₂) : actObj X M₁ ⟶ actObj X M₂
  actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) : actObj X₁ N ⟶ actObj X₂ N
  actTensorHom {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actObj X₁ M₁ ⟶ actObj X₂ M₂ :=
    actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g
  actAssociator : ∀ (X Y : C) (N : M),
    actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  unitActFunctor : M ⥤ M
  unitActFunctor_obj : ∀ (N : M), unitActFunctor.obj N = actObj (𝟙_ C) N
  unitActEquivalence : unitActFunctor.IsEquivalence
  actWhiskerLeft_id : ∀ (X : C) (N : M), actWhiskerLeft X (𝟙 N) = 𝟙 (actObj X N) := by
    aesop_cat
  actId_whiskerRight : ∀ (X : C) (N : M), actWhiskerRight (𝟙 X) N = 𝟙 (actObj X N) := by
    aesop_cat
  actAssociator_naturality :
      ∀ {X₁ X₂ : C} {Y₁ Y₂ : C} {M₁ M₂ : M}
        (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : M₁ ⟶ M₂),
      actTensorHom (f ⊗ₘ g) h ≫ (actAssociator X₂ Y₂ M₂).hom =
        (actAssociator X₁ Y₁ M₁).hom ≫ actTensorHom f (actTensorHom g h) := by
    aesop_cat
  actPentagon : ∀ (X Y Z : C) (N : M),
      actWhiskerRight (α_ X Y Z).hom N ≫ (actAssociator X (Y ⊗ Z) N).hom ≫
        actWhiskerLeft X (actAssociator Y Z N).hom =
        (actAssociator (X ⊗ Y) Z N).hom ≫ (actAssociator X Y (actObj Z N)).hom := by
    aesop_cat

/-- Alias for `Definition_2_1_1_LeftModuleCategory` matching the textbook numbering in EGNO. -/
abbrev Definition_2_1_1 := @Definition_2_1_1_LeftModuleCategory

/-- The bare data of a left module category over `C`: the action bifunctor `actObj`, its
whiskerings and tensor of morphisms, the associator `actAssociator`, and the left unitor
`actLeftUnitor`, without the coherence axioms. -/
class LeftModuleCategoryStruct (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
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

namespace LeftModCat

export LeftModuleCategoryStruct (actObj actWhiskerLeft actWhiskerRight actTensorHom
  actAssociator actLeftUnitor)

scoped infixr:70 " ⊗ᵐ " => LeftModuleCategoryStruct.actObj

scoped infixr:81 " ◁ᵐ " => LeftModuleCategoryStruct.actWhiskerLeft

scoped infixl:81 " ▷ᵐ " => LeftModuleCategoryStruct.actWhiskerRight

scoped infixr:70 " ⊗ₘᵐ " => LeftModuleCategoryStruct.actTensorHom

scoped notation "actμ_" => LeftModuleCategoryStruct.actAssociator

scoped notation "actℓ_" => LeftModuleCategoryStruct.actLeftUnitor

end LeftModCat

open LeftModCat

/-- Definition 2.1.2 (EGNO): A left module category over a monoidal category `C` consists of
the data of a `LeftModuleCategoryStruct` together with bifunctoriality of the action, the
pentagon coherence axiom for the action associator, the triangle axiom relating the
associator and unitors, and naturality of the left unitor. -/
class LeftModuleCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] extends LeftModuleCategoryStruct C M where
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

attribute [reassoc] LeftModuleCategory.actTensorHom_def
attribute [reassoc, simp] LeftModuleCategory.actWhiskerLeft_id
attribute [reassoc, simp] LeftModuleCategory.actId_whiskerRight
attribute [reassoc (attr := simp)] LeftModuleCategory.actTensorHom_comp
attribute [reassoc] LeftModuleCategory.actAssociator_naturality
attribute [reassoc] LeftModuleCategory.actLeftUnitor_naturality
attribute [reassoc (attr := simp)] LeftModuleCategory.actPentagon
attribute [reassoc (attr := simp)] LeftModuleCategory.actTriangle

/-- Alias for `LeftModuleCategory` matching the textbook numbering in EGNO. -/
abbrev Definition_2_1_2 := @LeftModuleCategory

/-- Definition 2.1.6 (EGNO): A predicate `P : M → Prop` defines a module subcategory of the
left module category `M` if it is closed under the action of `C`, i.e. `P N` implies
`P (X ⊗ᵐ N)` for every `X : C`. -/
class IsModuleSubcategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  closed_under_action : ∀ (X : C) (N : M), P N → P (X ⊗ᵐ N)

/-- Alias for `IsModuleSubcategory` matching the textbook numbering in EGNO. -/
abbrev Definition_2_1_6 := @IsModuleSubcategory

/-- A module functor between left `C`-module categories `M₁` and `M₂`: an underlying functor
together with a natural isomorphism `F(X ⊗ N) ≅ X ⊗ F(N)` compatible with the action
associator and left unitor. -/
structure ModuleFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] where
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

attribute [reassoc] ModuleFunctor.strIso_natural
attribute [reassoc (attr := simp)] ModuleFunctor.strIso_assoc
attribute [reassoc (attr := simp)] ModuleFunctor.strIso_unit

/-- Definition 2.12.1 (EGNO): A module natural transformation between module functors `F, G`
is an underlying natural transformation `F ⟶ G` compatible with the module structure
isomorphisms, i.e. `η_{X ⊗ N} ≫ G.strIso = F.strIso ≫ X ◁ᵐ η_N`. -/
structure ModuleNatTrans
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [LeftModuleCategory C M₂]
    (F G : ModuleFunctor C M₁ M₂) where
  toNatTrans : F.toFunctor ⟶ G.toFunctor
  compatibility : ∀ (X : C) (N : M₁),
    toNatTrans.app (X ⊗ᵐ N) ≫ (G.strIso X N).hom =
      (F.strIso X N).hom ≫ X ◁ᵐ (toNatTrans.app N)

attribute [reassoc] ModuleNatTrans.compatibility

/-- Alias for `ModuleNatTrans` matching the textbook numbering in EGNO. -/
abbrev Definition_2_12_1 := @ModuleNatTrans

/-- An equivalence of left `C`-module categories: a `ModuleFunctor` whose underlying functor
is an equivalence of categories. -/
structure ModuleEquivalence
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] extends
    ModuleFunctor C M₁ M₂ where
  isEquivalence : toFunctor.IsEquivalence

/-- Alias for `ModuleFunctor` matching the textbook numbering of Definition 2.2.1 in EGNO. -/
abbrev Definition_2_2_1 := @ModuleFunctor

end CategoryTheory
