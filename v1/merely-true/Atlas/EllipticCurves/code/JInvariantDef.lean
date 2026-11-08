/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

namespace JInvariant

variable {k : Type*} [Field k]

/-- The short Weierstrass curve $y^2 = x^3 + Ax + B$ given by setting $a_1 = a_2 = a_3 = 0$,
$a_4 = A$, $a_6 = B$. -/
def shortWeierstrassCurve (A B : k) : WeierstrassCurve k :=
  ⟨0, 0, 0, A, B⟩

/-- Definition 13.11. The $j$-invariant of the short Weierstrass curve $y^2 = x^3 + Ax + B$:
$j(A, B) = 1728 \cdot 4A^3 / (4A^3 + 27B^2)$. -/
def jInvariant (A B : k) : k :=
  1728 * (4 * A ^ 3) / (4 * A ^ 3 + 27 * B ^ 2)

/-- The $c_4$ invariant of the short Weierstrass curve $y^2 = x^3 + Ax + B$ equals $-48 A$. -/
@[simp]
lemma shortWeierstrassCurve_c₄ (A B : k) :
    (shortWeierstrassCurve A B).c₄ = -48 * A := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

/-- The discriminant of the short Weierstrass curve $y^2 = x^3 + Ax + B$ equals
$-16(4A^3 + 27B^2)$. -/
@[simp]
lemma shortWeierstrassCurve_Δ (A B : k) :
    (shortWeierstrassCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- If $2 \ne 0$ in $k$, then $16 \ne 0$ in $k$. -/
lemma sixteen_ne_zero_of_two_ne_zero (h2 : (2 : k) ≠ 0) : (16 : k) ≠ 0 := by
  have : (16 : k) = 2 ^ 4 := by norm_num
  rw [this]; exact pow_ne_zero 4 h2

/-- A short Weierstrass curve $y^2 = x^3 + Ax + B$ is elliptic provided $2 \ne 0$ in $k$ and
$4A^3 + 27B^2 \ne 0$. -/
lemma shortWeierstrassCurve_isElliptic (A B : k)
    (h2 : (2 : k) ≠ 0) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    (shortWeierstrassCurve A B).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, shortWeierstrassCurve_Δ]
  exact mul_ne_zero (neg_ne_zero.mpr (sixteen_ne_zero_of_two_ne_zero h2)) hΔ

/-- Mathlib's $j$-invariant of the short Weierstrass curve agrees with the textbook
formula $1728 \cdot 4A^3 / (4A^3 + 27B^2)$. -/
theorem j_eq_jInvariant (A B : k) (h2 : (2 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    haveI := shortWeierstrassCurve_isElliptic A B h2 hΔ
    (shortWeierstrassCurve A B).j = jInvariant A B := by
  haveI := shortWeierstrassCurve_isElliptic A B h2 hΔ
  simp only [WeierstrassCurve.j, jInvariant]
  have hΔ_val : ((shortWeierstrassCurve A B).Δ' : k) = (shortWeierstrassCurve A B).Δ :=
    WeierstrassCurve.coe_Δ' _
  simp only [Units.val_inv_eq_inv_val, hΔ_val, shortWeierstrassCurve_Δ,
    shortWeierstrassCurve_c₄]
  have h16 : (16 : k) ≠ 0 := sixteen_ne_zero_of_two_ne_zero h2
  field_simp
  ring

/-- When $A = 0$, the curve $y^2 = x^3 + B$ has $j$-invariant $0$. -/
@[simp]
theorem jInvariant_of_A_eq_zero (B : k) :
    jInvariant (0 : k) B = 0 := by
  simp [jInvariant]

/-- When $B = 0$ and $A \ne 0$, the curve $y^2 = x^3 + Ax$ has $j$-invariant $1728$. -/
theorem jInvariant_of_B_eq_zero (A : k) (hA : A ≠ 0) (h2 : (2 : k) ≠ 0) :
    jInvariant A (0 : k) = 1728 := by
  simp only [jInvariant, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero]
  rw [mul_div_cancel_right₀]
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2
  exact mul_ne_zero h4 (pow_ne_zero 3 hA)

end JInvariant
