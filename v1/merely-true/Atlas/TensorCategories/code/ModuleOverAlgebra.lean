/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 2.9.5 (EGNO): A right module structure on `M : C` over an algebra object
`A` consists of an action morphism `act : M ⊗ A ⟶ M` that is associative with respect to the
multiplication of `A` and unital with respect to the unit of `A`. -/
structure Definition_2_9_5 (A : C) [MonObj A] (M : C) where
  act : M ⊗ A ⟶ M
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

/-- The predicate that a morphism `l : M₁ ⟶ M₂` commutes with the right `A`-module actions
on `M₁` and `M₂`, i.e. `p₁.act ≫ l = (l ▷ A) ≫ p₂.act`. -/
def IsAModuleHom {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) (l : M₁ ⟶ M₂) : Prop :=
  p₁.act ≫ l = (l ▷ A) ≫ p₂.act

/-- A bundled module hom between two `A`-modules `(M₁, p₁)` and `(M₂, p₂)`: a morphism
`hom : M₁ ⟶ M₂` together with the commutativity condition with the actions. -/
@[ext]
structure AModuleHom {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) where
  hom : M₁ ⟶ M₂
  comm : p₁.act ≫ hom = (hom ▷ A) ≫ p₂.act := by aesop_cat

attribute [reassoc] AModuleHom.comm

/-- Alias for `AModuleHom` matching the textbook numbering of Definition 2.9.6 (morphisms
of right `A`-modules) in EGNO. -/
abbrev Definition_2_9_6 {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) :=
  AModuleHom p₁ p₂

namespace AModuleHom

variable {A : C} [MonObj A] {M₁ M₂ M₃ : C}
  {p₁ : Definition_2_9_5 A M₁} {p₂ : Definition_2_9_5 A M₂}
  {p₃ : Definition_2_9_5 A M₃}

/-- The identity module hom on an `A`-module `(M₁, p)`, given by the identity morphism. -/
@[simps]
def id (p : Definition_2_9_5 A M₁) : AModuleHom p p where
  hom := 𝟙 M₁
  comm := by simp

/-- Composition of module homs: the underlying morphisms are composed and the compatibility
square with the actions is verified. -/
@[simps]
def comp (f : AModuleHom p₁ p₂) (g : AModuleHom p₂ p₃) : AModuleHom p₁ p₃ where
  hom := f.hom ≫ g.hom
  comm := by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc,
        (comp_whiskerRight f.hom g.hom A).symm]

end AModuleHom

/-- Alias for `IsMod_Hom` matching the textbook numbering of Definition 2.9.6 in the
left-module setting, expressed via Mathlib's `ModObj` typeclass. -/
abbrev Definition_2_9_6_left (A : C) [MonObj A] {M N : C}
    [ModObj A M] [ModObj A N] (f : M ⟶ N) :=
  IsMod_Hom A f


end CategoryTheory
