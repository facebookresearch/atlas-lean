/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HomExactImpliesExact

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Proposition 2.10.7 (EGNO), part 1: A module category `M` over `C` is exact whenever
the internal Hom is exact in its second variable. -/
abbrev Proposition_2_10_7_part1
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  proposition_2_10_7_part1 h


/-- Proposition 2.10.7 (EGNO): Convenient alias bundling the first criterion for a
module category to be exact, namely exactness of the internal Hom in its second
argument. -/
abbrev Proposition_2_10_7
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  Proposition_2_10_7_part1 h

end CategoryTheory
