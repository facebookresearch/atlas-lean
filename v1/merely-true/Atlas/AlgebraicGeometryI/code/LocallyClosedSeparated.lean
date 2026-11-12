/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Immersion

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- If `X` is a separated scheme and `f : Z ⟶ X` is an immersion (in particular
locally closed), then `Z` is also separated (Lem 17, Lec 7). -/
theorem isSeparated_of_isImmersion
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] [X.IsSeparated] :
    Z.IsSeparated := by
  constructor

  rw [show terminal.from Z = f ≫ terminal.from X from terminal.hom_ext _ _]


  infer_instance

/-- The composition of an immersion with a separated morphism is separated. -/
theorem isSeparated_comp_of_isImmersion
    {Z X S : Scheme.{u}} (f : Z ⟶ X) (g : X ⟶ S)
    [IsImmersion f] [IsSeparated g] :
    IsSeparated (f ≫ g) := by

  infer_instance

end AlgebraicGeometry
