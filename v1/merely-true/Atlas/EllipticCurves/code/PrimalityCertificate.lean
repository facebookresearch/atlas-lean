/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ECPrimality

/-- The short Weierstrass curve $y^2 = x^3 + Ax + B$ over a commutative ring $R$. -/
def shortWeierstrass (R : Type*) [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, A, B⟩

/-- The affine short Weierstrass curve $y^2 = x^3 + Ax + B$ reduced modulo $n$. -/
def curveModN (n : ℕ) (A B : ℤ) : WeierstrassCurve.Affine (ZMod n) :=
  (shortWeierstrass (ZMod n) (↑A) (↑B)).toAffine

end ECPrimality

/-- A *Goldwasser-Kilian primality certificate* (Definition 11.14) for a positive
integer $p > 1$.  It bundles:

* short Weierstrass coefficients $A, B \in \mathbb{Z}$ defining a curve $E$,
* an affine point $(x_1, y_1)$ on $E$,
* an integer $q > (p^{1/4} + 1)^2$,
* a proof that the discriminant $-16(4A^3 + 27B^2)$ is coprime to $p$,
* a proof that the reduction of $(x_1, y_1)$ mod $p$ is nonsingular, and
* a proof that $q \cdot (x_1, y_1) = O$ in $E(\mathbb{Z}/p\mathbb{Z})$ whenever $p$ is prime.

By Theorem 11.13 the existence of such a certificate implies $p$ is prime. -/
structure PrimalityCertificate where
  p : ℤ
  A : ℤ
  B : ℤ
  x₁ : ℤ
  y₁ : ℤ
  q : ℤ
  hp : 1 < p
  hq : (q : ℝ) > ((p : ℝ) ^ (1/4 : ℝ) + 1) ^ 2
  on_curve : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B
  coprime_disc : Int.gcd p (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = 1
  point_nonsingular :
    (ECPrimality.curveModN p.toNat A B).Nonsingular (↑x₁ : ZMod p.toNat) (↑y₁)
  hqP_zero :
    ∀ (hp_prime : Nat.Prime p.toNat),
    letI : Fact (Nat.Prime p.toNat) := ⟨hp_prime⟩
    q • (WeierstrassCurve.Affine.Point.some
      (↑x₁ : ZMod p.toNat) (↑y₁) point_nonsingular) =
    (0 : (ECPrimality.curveModN p.toNat A B).Point)
