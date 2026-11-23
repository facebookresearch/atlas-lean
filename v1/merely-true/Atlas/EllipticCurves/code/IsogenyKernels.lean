/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.LinearCombination

open Polynomial

/-- **Lemma 5.1, first equivalence.**  For coprime polynomials $u, v$ over a
field $k$, the Wronskian $W(u, v) = u v' - u' v$ vanishes iff both $u$ and $v$
are constant (have zero derivative). -/
theorem lemma_5_1_first_iff {k : Type*} [Field k] {u v : k[X]}
    (hcop : IsCoprime u v) :
    u.wronskian v = 0 ↔ derivative u = 0 ∧ derivative v = 0 :=
  hcop.wronskian_eq_zero_iff

/-- **Lemma 5.1, second equivalence.**  Over a field $k$, a polynomial $u$ has
zero derivative iff it is a $p$-th power (in the sense of being in the image of
the Frobenius `expand` map), where $p = \mathrm{char}\, k$ (with the convention
$p = 0$ giving the constant polynomials). -/
theorem lemma_5_1_second_iff {k : Type*} [Field k] (u : k[X]) :
    derivative u = 0 ↔ ∃ g : k[X], expand k (ringChar k) g = u := by
  constructor
  · intro hu
    by_cases hp : ringChar k = 0
    ·
      haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hp
      rw [hp]
      have hdeg : u.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hu
      rw [eq_C_of_natDegree_eq_zero hdeg]
      exact ⟨C (u.coeff 0), by simp⟩
    ·
      haveI : CharP k (ringChar k) := ringChar.charP k
      exact ⟨contract (ringChar k) u, expand_contract (ringChar k) hu hp⟩
  ·
    intro ⟨g, hg⟩
    rw [← hg, derivative_expand]
    have : (ringChar k : k[X]) = 0 := by rw [← C_eq_natCast]; simp
    rw [this, zero_mul, mul_zero]

/-- **Lemma 5.1.**  For coprime polynomials $u, v$ over a field $k$, the
Wronskian $W(u, v)$ vanishes iff both $u$ and $v$ are $p$-th powers (in the
sense of `expand`), where $p = \mathrm{char}\, k$. -/
theorem lemma_5_1 {k : Type*} [Field k] {u v : k[X]}
    (hcop : IsCoprime u v) :
    u.wronskian v = 0 ↔
      (∃ f : k[X], expand k (ringChar k) f = u) ∧
      (∃ g : k[X], expand k (ringChar k) g = v) := by
  rw [lemma_5_1_first_iff hcop]
  exact ⟨fun ⟨hu, hv⟩ =>
      ⟨(lemma_5_1_second_iff u).mp hu, (lemma_5_1_second_iff v).mp hv⟩,
    fun ⟨hu, hv⟩ =>
      ⟨(lemma_5_1_second_iff u).mpr hu, (lemma_5_1_second_iff v).mpr hv⟩⟩

namespace Velu

variable {k : Type*} [Field k]

/-- A *short Weierstrass curve* $y^2 = x^3 + A x + B$, recorded by its
coefficients $A, B \in k$. -/
structure ShortWeierstrassCurve (k : Type*) where
  A : k
  B : k

/-- An *affine point* $(x, y)$ on a short Weierstrass curve $E$, together with
a proof that it satisfies the curve equation $y^2 = x^3 + A x + B$. -/
structure AffinePoint (E : ShortWeierstrassCurve k) where
  x : k
  y : k
  on_curve : y ^ 2 = x ^ 3 + E.A * x + E.B

variable {E : ShortWeierstrassCurve k}

/-- Input data for the *Vélu degree-2* isogeny construction: a $k$-rational
$2$-torsion point $(x_0, 0)$ on $E$, encoded by $x_0$ together with a proof
that $x_0$ is a root of the cubic $x^3 + A x + B$. -/
structure VeluDeg2Data (E : ShortWeierstrassCurve k) where
  x₀ : k
  is_root : x₀ ^ 3 + E.A * x₀ + E.B = 0

namespace VeluDeg2Data

variable (d : VeluDeg2Data E)

/-- Vélu's degree-2 parameter $t = 3 x_0^2 + A$ (twice the slope of the tangent
at the kernel point). -/
def t : k := 3 * d.x₀ ^ 2 + E.A

/-- Vélu's degree-2 parameter $w = x_0 \cdot t$. -/
def w : k := d.x₀ * d.t

/-- New $A$-coefficient $A' = A - 5 t$ of the Vélu degree-2 image curve. -/
def A' : k := E.A - 5 * d.t

/-- New $B$-coefficient $B' = B - 7 w$ of the Vélu degree-2 image curve. -/
def B' : k := E.B - 7 * d.w

/-- The *image curve* $E' : y^2 = x^3 + A' x + B'$ produced by Vélu's
degree-2 formula. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- The $A$-coefficient of the Vélu degree-2 image curve unfolds to $A'$. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl
/-- The $B$-coefficient of the Vélu degree-2 image curve unfolds to $B'$. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

/-- The $x$-coordinate of the Vélu degree-2 isogeny:
$\varphi_x(x) = \frac{x^2 - x_0 x + t}{x - x_0}$. -/
noncomputable def φ_x (x : k) : k := (x ^ 2 - d.x₀ * x + d.t) / (x - d.x₀)

/-- Multiplier appearing in the $y$-coordinate of the Vélu degree-2 isogeny:
$\frac{(x - x_0)^2 - t}{(x - x_0)^2}$, so that $\varphi_y(x, y) = y \cdot
\frac{(x - x_0)^2 - t}{(x - x_0)^2}$. -/
noncomputable def φ_y_coeff (x : k) : k := ((x - d.x₀) ^ 2 - d.t) / (x - d.x₀) ^ 2

/-- The kernel point $(x_0, 0)$ satisfies the curve equation
$y^2 = x^3 + A x + B$ with $y = 0$ since $x_0$ is a root of the cubic. -/
lemma kernel_point_on_curve : (0 : k) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B := by
  linear_combination -d.is_root

/-- The (generator of the) Vélu degree-2 kernel: the $2$-torsion point $(x_0, 0)$
on $E$. -/
def kernelPoint : AffinePoint E :=
  ⟨d.x₀, 0, d.kernel_point_on_curve⟩

end VeluDeg2Data

/-- Vélu's per-point parameter $t_Q = 3 x_Q^2 + A$ at the point $Q = (x_Q, y_Q)$. -/
def AffinePoint.tQ (Q : AffinePoint E) : k := 3 * Q.x ^ 2 + E.A

/-- Vélu's per-point parameter $u_Q = 2 y_Q^2$ at the point $Q$. -/
def AffinePoint.uQ (Q : AffinePoint E) : k := 2 * Q.y ^ 2

/-- Vélu's per-point parameter $w_Q = u_Q + t_Q x_Q$ at the point $Q$. -/
def AffinePoint.wQ (Q : AffinePoint E) : k := Q.uQ + Q.tQ * Q.x

/-- Unfolding $t_Q$. -/
@[simp] lemma AffinePoint.tQ_val (Q : AffinePoint E) :
    Q.tQ = 3 * Q.x ^ 2 + E.A := rfl

/-- Unfolding $u_Q$. -/
@[simp] lemma AffinePoint.uQ_val (Q : AffinePoint E) :
    Q.uQ = 2 * Q.y ^ 2 := rfl

/-- Unfolding $w_Q$. -/
@[simp] lemma AffinePoint.wQ_val (Q : AffinePoint E) :
    Q.wQ = Q.uQ + Q.tQ * Q.x := rfl

/-- Expanded form $w_Q = 2 y_Q^2 + (3 x_Q^2 + A) x_Q$. -/
lemma AffinePoint.wQ_expanded (Q : AffinePoint E) :
    Q.wQ = 2 * Q.y ^ 2 + (3 * Q.x ^ 2 + E.A) * Q.x := rfl

/-- Using the curve equation, $u_Q = 2(x_Q^3 + A x_Q + B)$. -/
lemma AffinePoint.uQ_eq_curve (Q : AffinePoint E) :
    Q.uQ = 2 * (Q.x ^ 3 + E.A * Q.x + E.B) := by
  simp only [AffinePoint.uQ]
  linear_combination 2 * Q.on_curve

/-- Using the curve equation, $w_Q = 5 x_Q^3 + 3 A x_Q + 2 B$. -/
lemma AffinePoint.wQ_eq_curve (Q : AffinePoint E) :
    Q.wQ = 5 * Q.x ^ 3 + 3 * E.A * Q.x + 2 * E.B := by
  simp only [AffinePoint.wQ, AffinePoint.uQ, AffinePoint.tQ]
  linear_combination 2 * Q.on_curve

/-- Input data for *Vélu's odd-degree* isogeny construction: a finite set
$\{Q_1, \dots, Q_n\}$ of affine points (representatives modulo $\pm$), such
that the resulting kernel has odd order $n + 1$ (i.e.\ the cardinality of `pts`
plus one is odd). -/
structure VeluOddData (E : ShortWeierstrassCurve k) where
  pts : Finset (AffinePoint E)
  odd_order : Odd (pts.card + 1)

namespace VeluOddData

variable (d : VeluOddData E)

/-- Aggregated Vélu parameter $t = \sum_Q t_Q$ over the (odd-order) kernel. -/
def t : k := d.pts.sum (fun Q => Q.tQ)

/-- Aggregated Vélu parameter $w = \sum_Q w_Q$ over the (odd-order) kernel. -/
def w : k := d.pts.sum (fun Q => Q.wQ)

/-- New $A$-coefficient $A' = A - 5 t$ of the Vélu odd-degree image curve. -/
def A' : k := E.A - 5 * d.t

/-- New $B$-coefficient $B' = B - 7 w$ of the Vélu odd-degree image curve. -/
def B' : k := E.B - 7 * d.w

/-- The Vélu odd-degree *image curve* $E' : y^2 = x^3 + A' x + B'$. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- The $A$-coefficient of the Vélu odd-degree image curve unfolds to $A'$. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl
/-- The $B$-coefficient of the Vélu odd-degree image curve unfolds to $B'$. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

/-- The Vélu odd-degree rational function on $x$-coordinates:
$r(x) = x + \sum_{Q} \left( \frac{t_Q}{x - x_Q} + \frac{u_Q}{(x - x_Q)^2} \right)$. -/
noncomputable def r (x : k) : k :=
  x + d.pts.sum (fun Q => Q.tQ / (x - Q.x) + Q.uQ / (x - Q.x) ^ 2)

/-- Derivative of the Vélu rational function:
$r'(x) = 1 - \sum_{Q} \left( \frac{t_Q}{(x - x_Q)^2} + \frac{2 u_Q}{(x - x_Q)^3} \right)$. -/
noncomputable def r' (x : k) : k :=
  1 + d.pts.sum (fun Q => -(Q.tQ / (x - Q.x) ^ 2) - 2 * Q.uQ / (x - Q.x) ^ 3)




end VeluOddData

end Velu
