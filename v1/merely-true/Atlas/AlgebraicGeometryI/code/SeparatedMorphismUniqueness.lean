/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.RationalMap

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Uniqueness of morphisms to a separated scheme: two maps `f, g : X → Y`
from an irreducible reduced scheme `X` into a separated scheme `Y` that
agree on a nonempty open subscheme are equal. -/
theorem eq_of_agree_on_nonempty_open
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IsReduced X] [Y.IsSeparated]
    {f g : X ⟶ Y} (U : X.Opens) (hU_ne : (U : Set X).Nonempty)
    (h_agree : U.ι ≫ f = U.ι ≫ g) : f = g := by

  have hU_dense : Dense (X := X) (U : Set X) := U.isOpen.dense hU_ne

  haveI : IsDominant U.ι := Scheme.PartialMap.Opens.isDominant_ι hU_dense


  exact ext_of_isDominant U.ι h_agree

/-- Relative version of uniqueness: two `S`-morphisms `g, h : X → Y` from
an irreducible reduced scheme `X` that agree on a nonempty open subscheme
are equal, provided `Y → S` is separated. -/
theorem eq_of_agree_on_nonempty_open_over_base
    {X Y S : Scheme.{u}} [IrreducibleSpace X] [IsReduced X]
    {s : Y ⟶ S} [IsSeparated s]
    {g h : X ⟶ Y} (hs : g ≫ s = h ≫ s)
    (U : X.Opens) (hU_ne : (U : Set X).Nonempty)
    (h_agree : U.ι ≫ g = U.ι ≫ h) : g = h := by
  have hU_dense : Dense (X := X) (U : Set X) := U.isOpen.dense hU_ne
  haveI : IsDominant U.ι := Scheme.PartialMap.Opens.isDominant_ι hU_dense
  exact ext_of_isDominant_of_isSeparated s hs U.ι h_agree

end AlgebraicGeometry

end
