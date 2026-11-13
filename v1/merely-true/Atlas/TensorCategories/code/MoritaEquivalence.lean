/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Monoidal.Mod_

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

/-- Two left module categories `ModA` and `ModB` over `C` are Morita equivalent if there
exists an equivalence of module categories between them. -/
def IsMoritaEquivalent
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (ModA : Type u₂) [Category.{v₂} ModA] [LeftModuleCategory' C ModA]
    (ModB : Type u₃) [Category.{v₃} ModB] [LeftModuleCategory' C ModB] : Prop :=
  Nonempty (ModuleEquivalence' C ModA ModB)





end CategoryTheory
