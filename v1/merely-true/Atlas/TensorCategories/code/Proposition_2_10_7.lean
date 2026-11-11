/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HomExactImpliesExact

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Proposition_2_10_7

open Category MonoidalCategory LeftModCat

/-- Proposition 2.10.7, part (1): If the internal `Hom` bifunctor on a module category `M`
over `C` is exact in the second variable, then `M` is an exact module category. -/
noncomputable def part1
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  proposition_2_10_7_part1 h


end Proposition_2_10_7

end CategoryTheory
