/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category

open CategoryTheory MonoidalCategory

universe u v

namespace Definition_1_15_4

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Given a finite indexing `f : Fin n → C` of objects (typically the components of the unit
object), this is the object `f i ⊗ X ⊗ f j` used to define the component subcategory C_{ij}. -/
def componentObj {n : ℕ} (f : Fin n → C) (X : C) (i j : Fin n) : C :=
  f i ⊗ X ⊗ f j

/-- Predicate: X belongs to the component subcategory C_{ij} := 1_i ⊗ C ⊗ 1_j, i.e., there
exists some Y in C with X isomorphic to f i ⊗ Y ⊗ f j. -/
def IsInComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    ObjectProperty C :=
  fun X => ∃ (Y : C), Nonempty (X ≅ f i ⊗ Y ⊗ f j)

/-- Definition 1.15.4: The component subcategory C_{ij} := 1_i ⊗ C ⊗ 1_j of a multiring
category, realized as the full subcategory on objects satisfying `IsInComponentSubcategory f i j`. -/
abbrev ComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :=
  (IsInComponentSubcategory f i j).FullSubcategory

/-- The component subcategory inherits the category structure from C via its full subcategory
structure. -/
instance componentSubcategory_category {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    Category (ComponentSubcategory f i j) := inferInstance

end Definition_1_15_4
