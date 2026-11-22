/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory
import Atlas.TensorCategories.code.FiniteTensorCategory
import Mathlib.CategoryTheory.Monoidal.Mod_

set_option maxHeartbeats 400000

universe w v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [FiniteTensorCategory k C]

/-- An algebra `A` in a finite tensor category `C` is exact when its category of left
modules `Mod_C A` is an exact module category over `C`. -/
def IsExactAlgebra_FiniteTensor (A : C) [MonObj A] : Prop :=
  Nonempty (ExactModuleCategory C (Mod_ C A))

/-- Definition 2.9.18 (exact algebra): an algebra `A ∈ C` is exact in the sense that
its module category is an exact module category over `C`. -/
@[reducible] def Definition_2_9_18_ExactAlgebra (A : C) [MonObj A] : Prop :=
  IsExactAlgebra_FiniteTensor (k := k) A

/-- Definition 2.9.21: alias of the exact-algebra predicate; an algebra `A ∈ C` whose
category of modules is an exact module category over `C`. -/
@[reducible] def Definition_2_9_21 (A : C) [MonObj A] : Prop :=
  IsExactAlgebra_FiniteTensor (k := k) A

end CategoryTheory
