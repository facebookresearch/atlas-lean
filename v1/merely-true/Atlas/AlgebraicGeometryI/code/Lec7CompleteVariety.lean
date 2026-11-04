/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Formalization.Lec7CompleteVariety

/-- A morphism `f : X ⟶ S` is a complete variety if it is separated
and universally closed (Lec 7/8, Def 19 / Lem 19 setting). -/
class IsCompleteVariety {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  isSeparated : IsSeparated f
  universallyClosed : UniversallyClosed f

/-- A proper morphism is a complete variety. -/
instance isCompleteVariety_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] : IsCompleteVariety f where
  isSeparated := inferInstance
  universallyClosed := inferInstance

/-- A complete variety that is locally of finite type is proper. -/
theorem isProper_of_isCompleteVariety {X S : Scheme.{u}} (f : X ⟶ S)
    [hc : IsCompleteVariety f] [LocallyOfFiniteType f] : IsProper f where
  toIsSeparated := hc.isSeparated
  toUniversallyClosed := hc.universallyClosed

end Formalization.Lec7CompleteVariety
