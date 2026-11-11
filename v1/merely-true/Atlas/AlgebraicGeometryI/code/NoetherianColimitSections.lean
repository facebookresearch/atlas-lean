/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Filtered.Basic

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite

/-- The functor sending a sheaf to its sections over a fixed open `U`. -/
noncomputable def TopCat.Sheaf.sectionsAt
    (C : Type u) [Category.{v} C] {X : TopCat.{w}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ C :=
  TopCat.Sheaf.forget C X ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op U)


