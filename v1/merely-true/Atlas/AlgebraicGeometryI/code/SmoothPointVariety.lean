/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

section SmoothPointDefinition

/-- A locally Noetherian scheme `X` is **smooth at a point `x`** if the local
ring `O_{X,x}` is a regular local ring. -/
def Scheme.IsSmoothAtPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

/-- `X` is **singular at `x`** if it is not smooth at `x`. -/
def Scheme.IsSingularAtPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Prop :=
  ¬ Scheme.IsSmoothAtPoint X x

/-- `X` is **smooth** if it is smooth at every point. -/
def Scheme.IsSmooth (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ x : X, Scheme.IsSmoothAtPoint X x

end SmoothPointDefinition

section SmoothPointProperties

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Smoothness at `x` is by definition regularity of the local ring `O_{X,x}`. -/
theorem Scheme.isSmoothAtPoint_iff_isRegularLocalRing (x : X) :
    Scheme.IsSmoothAtPoint X x ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- Smoothness criterion via the minimal number of generators of the maximal
ideal: `X` is smooth at `x` iff `spanFinrank(𝔪_x) = dim O_{X,x}`. -/
theorem Scheme.isSmoothAtPoint_iff_spanFinrank (x : X)
    [IsLocalRing (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)] :
    Scheme.IsSmoothAtPoint X x ↔
      (maximalIdeal (X.presheaf.stalk x)).spanFinrank =
        ringKrullDim (X.presheaf.stalk x) := by
  unfold Scheme.IsSmoothAtPoint
  exact isRegularLocalRing_iff (X.presheaf.stalk x)

/-- Smoothness via the cotangent space: `X` is smooth at `x` iff
`dim_κ(𝔪_x/𝔪_x²) = dim O_{X,x}`. This is the classical "Zariski tangent space
of expected dimension" criterion. -/
theorem Scheme.isSmoothAtPoint_iff_finrank_cotangentSpace (x : X)
    [IsLocalRing (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)] :
    Scheme.IsSmoothAtPoint X x ↔
      (Module.finrank (ResidueField (X.presheaf.stalk x))
        (CotangentSpace (X.presheaf.stalk x)) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) := by
  unfold Scheme.IsSmoothAtPoint
  exact IsRegularLocalRing.iff_finrank_cotangentSpace (R := (X.presheaf.stalk x))

end SmoothPointProperties

end
