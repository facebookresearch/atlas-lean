/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w v u t

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}
variable {J : Type t} [Category.{t} J] [IsFiltered J]

/-- The diagram of sections at a fixed open `U` of a `J`-shaped diagram of sheaves. -/
def sectionsAtU
    (F : J ⥤ TopCat.Sheaf C X) (U : (Opens (X : TopCat.{w}))ᵒᵖ) : J ⥤ C :=
  F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C ⋙
    (evaluation (Opens (X : TopCat.{w}))ᵒᵖ C).obj U



end TopCat.Sheaf
