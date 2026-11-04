/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory

open CategoryTheory MonoidalCategory LeftModCat

namespace CategoryTheory

universe u₁ v₁ u₂ v₂

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
variable (M_cat : Type u₂) [Category.{v₂} M_cat] [LeftModuleCategory C M_cat]

/-- The hypotheses needed for Theorem 2.11.2: a generator object `gen` of `M_cat`, a target
module category `D`, and an epi-preserving module functor `F : M_cat ⥤ D` such that every
object of `M_cat` is the target of an epimorphism from some `X ⊗ᵐ gen`. -/
structure InternalHomConditions
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M_cat : Type u₂) [Category.{v₂} M_cat] [LeftModuleCategory C M_cat] where
  gen : M_cat
  D : Type (max u₁ u₂)
  [catD : Category.{max v₁ v₂} D]
  [modD : LeftModuleCategory C D]
  F : M_cat ⥤ D
  preservesEpi : ∀ {N₁ N₂ : M_cat} (f : N₁ ⟶ N₂), Epi f → Epi (F.map f)
  generation : ∀ (N : M_cat), ∃ (X : C) (f : X ⊗ᵐ gen ⟶ N), Epi f


end CategoryTheory
