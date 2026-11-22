/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.WeierstrassP
import Atlas.EllipticCurves.code.Uniformization
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Complex

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass curve `E_L : y^2 = 4x^3 - g₂(L)·x - g₃(L)` associated to a
lattice `L`, presented in long Weierstrass form with coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -g₂/4, -g₃/4)`. -/
def ellipticCurveEL : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- The affine model of `ellipticCurveEL L`, used to talk about its affine
`Point` type. -/
def ellipticCurveEL_affine : WeierstrassCurve.Affine ℂ :=
  L.ellipticCurveEL.toAffine

/-- The type of points on the elliptic curve `E_L` associated to the lattice `L`. -/
abbrev ELPoint : Type := L.ellipticCurveEL_affine.Point

/-- The additive group structure on `E_L(ℂ)` from the chord-tangent law on a
Weierstrass curve. -/
instance : AddCommGroup L.ELPoint := by
  classical
  exact WeierstrassCurve.Affine.Point.instAddCommGroup

/-- The discriminant of the affine elliptic curve `E_L` equals the lattice
discriminant `Δ(L) = g₂³ - 27 g₃²` (up to the normalization built into
`discriminantLattice`). -/
lemma ellipticCurveEL_Δ_eq : L.ellipticCurveEL_affine.Δ = L.discriminantLattice := by
  unfold discriminantLattice ellipticCurveEL_affine ellipticCurveEL WeierstrassCurve.toAffine
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring


/-- For any non-lattice point `z`, the pair `(℘(z), ℘'(z)/2)` satisfies the
Weierstrass equation of `E_L`, i.e. lies on the affine curve. This is the
key calculation behind the uniformization map of Theorem 15.1. -/
lemma weierstrassP_point_equation (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    L.ellipticCurveEL_affine.Equation
      (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ellipticCurveEL_affine, ellipticCurveEL, WeierstrassCurve.toAffine]
  have h := L.weierstrassPFun_differentialEquation z hz
  simp only [g₂Fun_eq, g₃Fun_eq] at h

  simp only [zero_mul, add_zero]
  rw [div_pow, h]
  field_simp
  ring



/-- The complex torus `ℂ / L` for the lattice `L`. -/
abbrev complexTorus : Type := ℂ ⧸ L.toAddSubgroup

/-- The complex torus inherits the additive group structure from the quotient
of `ℂ` by `L`. -/
instance : AddCommGroup L.complexTorus :=
  QuotientAddGroup.Quotient.addCommGroup L.toAddSubgroup












end ComplexLattice

end
