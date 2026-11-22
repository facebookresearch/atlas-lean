/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.IsomorphismClasses

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- A `ModuleSubcategory` of `M` over `C`: a predicate `P : M → Prop` that is closed
under the action of `C` on `M`. -/
class ModuleSubcategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  closed_under_action : ∀ (X : C) (N : M), P N → P (X ⊗ᵐ N)

/-- An `IsModuleSubcategory` predicate yields a `ModuleSubcategory` instance. -/
instance moduleSubcategory_of_isModuleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) [h : IsModuleSubcategory C M P] : ModuleSubcategory C M P where
  closed_under_action := h.closed_under_action

/-- A `ModuleSubcategory` predicate yields an `IsModuleSubcategory` instance. -/
instance isModuleSubcategory_of_moduleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) [h : ModuleSubcategory C M P] : IsModuleSubcategory C M P where
  closed_under_action := h.closed_under_action

/-- Setoid on the subtype of simple objects of `M`, identifying objects related by an
isomorphism. -/
def simpleIsoSetoid (M : Type u₁) [Category.{v₁} M] [Limits.HasZeroMorphisms M] :
    Setoid {X : M // Simple X} where
  r := fun ⟨X, _⟩ ⟨Y, _⟩ => Nonempty (X ≅ Y)
  iseqv := ⟨fun ⟨X, _⟩ => ⟨Iso.refl X⟩,
            fun ⟨f⟩ => ⟨f.symm⟩,
            fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- The set of isomorphism classes of simple objects of `M`. -/
def SimpleIsoClasses (M : Type u₁) [Category.{v₁} M] [Limits.HasZeroMorphisms M] : Type u₁ :=
  _root_.Quotient (simpleIsoSetoid M)

/-- The rank of a module category `M`: the number of isomorphism classes of simple
objects, defined when this set is finite. -/
noncomputable def moduleCategoryRank (M : Type u₁) [Category.{v₁} M]
    [Limits.HasZeroMorphisms M] [Fintype (SimpleIsoClasses M)] : ℕ :=
  Fintype.card (SimpleIsoClasses M)

end CategoryTheory
