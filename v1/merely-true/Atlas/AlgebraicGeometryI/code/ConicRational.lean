/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRoch
import Atlas.AlgebraicGeometryI.code.PicardProjective
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.AdjoinRoot

namespace ConicRational


section General

variable (R : Type*) [CommRing R]

/-- The polynomial `r·X - 1`, whose root in an extension inverts `r`. -/
noncomputable def invertPoly (r : R) : Polynomial R :=
  Polynomial.C r * Polynomial.X - 1

/-- The localization `R[1/r]` is `R`-algebra isomorphic to `R[X]/(rX - 1)`. -/
noncomputable def localizationEquivAdjoinRoot (r : R) :
    Localization.Away r ≃ₐ[R] AdjoinRoot (invertPoly R r) :=
  Localization.awayEquivAdjoin r

/-- `R[X]/(rX-1)` is a localization of `R` away from `r`. -/
instance adjoinRoot_isLocalization (r : R) :
    IsLocalization.Away r (AdjoinRoot (invertPoly R r)) :=
  IsLocalization.adjoin_inv r

/-- The image of `r` times the adjoined root is `1` in `R[X]/(rX - 1)`. -/
theorem adjoinRoot_inv_relation (r : R) :
    AdjoinRoot.of (invertPoly R r) r * AdjoinRoot.root (invertPoly R r) = 1 :=
  AdjoinRoot.root_isInv r

end General


section Hyperbola

variable (k : Type*) [CommRing k]

/-- The hyperbola defining polynomial `X·Y - 1` as a polynomial in `Y` over `k[X]`. -/
noncomputable def hyperbolaPoly : Polynomial (Polynomial k) :=
  invertPoly (Polynomial k) Polynomial.X

/-- The hyperbola coordinate ring is the localization of `k[X]` at `X`. -/
instance hyperbolaIsLocalization :
    IsLocalization.Away (Polynomial.X : Polynomial k)
    (AdjoinRoot (hyperbolaPoly k)) :=
  adjoinRoot_isLocalization (Polynomial k) Polynomial.X

/-- The defining relation `xy = 1` in the hyperbola coordinate ring. -/
theorem hyperbola_xy_eq_one :
    AdjoinRoot.of (hyperbolaPoly k) Polynomial.X *
    AdjoinRoot.root (hyperbolaPoly k) = 1 :=
  adjoinRoot_inv_relation (Polynomial k) Polynomial.X

end Hyperbola


section Domain

variable (k : Type*) [Field k]

/-- Over a field, the powers of `X` are non-zero-divisors in `k[X]`. -/
theorem powers_X_le_nonZeroDivisors :
    Submonoid.powers (Polynomial.X : Polynomial k) ≤ nonZeroDivisors (Polynomial k) := by
  intro x ⟨n, hn⟩
  rw [mem_nonZeroDivisors_iff_ne_zero, ← hn]
  exact pow_ne_zero n Polynomial.X_ne_zero

/-- Over a field, the hyperbola coordinate ring `k[X, X⁻¹]` is an integral domain. -/
noncomputable instance hyperbolaIsDomain :
    IsDomain (AdjoinRoot (hyperbolaPoly k)) := by
  haveI : IsLocalization.Away (Polynomial.X : Polynomial k) (AdjoinRoot (hyperbolaPoly k)) :=
    adjoinRoot_isLocalization (Polynomial k) Polynomial.X
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _ (powers_X_le_nonZeroDivisors k)

end Domain


section ProjectiveConic

variable (k : Type*) [CommRing k]

/-- The defining polynomial of the projective conic `X·Y = Z²` in `P^2`. -/
noncomputable def conicPoly : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 ^ 2

end ProjectiveConic


section GenusRationality

/-- The genus-degree formula for a smooth plane curve of degree `d`: `g = (d-1)(d-2)/2`. -/
def genusDeg (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- A smooth conic (degree 2 plane curve) has genus zero. -/
theorem genus_conic_eq_zero : genusDeg 2 = 0 := by rfl

/-- Bridge identifying the conic's genus (from the degree formula) with the Riemann-Roch genus
`RiemannRoch.genus 2`. -/
theorem conic_genus_bridge : genusDeg 2 = RiemannRoch.genus 2 := by
  unfold genusDeg RiemannRoch.genus
  rfl

end GenusRationality


end ConicRational
