/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorDefs
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option maxHeartbeats 400000

set_option linter.all false

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

/-- A finite module category over `C`: an abelian left `C`-module category with enough
projectives, together with a representing algebra `repAlg : Mon C` so that `M` is equivalent
to modules over `repAlg`. -/
class FiniteModuleCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  abelianM : Nonempty (Abelian M)
  enoughProjM : EnoughProjectives M
  repAlg : Mon C


end CategoryTheory
