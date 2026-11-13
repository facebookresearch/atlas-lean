/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace EllipticCurveSmooth

variable {k : Type*} [Field k]

/-- The short Weierstrass curve `y² = x³ + a x + b` packaged as a `WeierstrassCurve`. -/
noncomputable def shortWeierstrass (a b : k) : WeierstrassCurve k where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

/-- The bivariate Weierstrass polynomial `Y² − (X³ + aX + b)`, viewed in `k[X][Y]`. -/
noncomputable def weierstrass (a b : k) : Polynomial (Polynomial k) :=
  Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b)

/-- Our hand-written Weierstrass polynomial agrees with the mathlib affine
defining polynomial. -/
lemma weierstrass_eq_polynomial (a b : k) :
    weierstrass a b = (shortWeierstrass a b).toAffine.polynomial := by
  unfold weierstrass shortWeierstrass WeierstrassCurve.Affine.polynomial
      WeierstrassCurve.toAffine
  simp only [map_zero, map_add, map_mul, zero_mul, add_zero]

/-- The Weierstrass polynomial is monic of degree two in `Y`. -/
lemma weierstrass_monic (a b : k) : (weierstrass a b).Monic := by
  unfold weierstrass
  apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
  calc (Polynomial.C (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) :
      Polynomial (Polynomial k)).degree
      ≤ 0 := Polynomial.degree_C_le
    _ < (Polynomial.X ^ 2 : Polynomial (Polynomial k)).degree := by simp

/-- The Weierstrass polynomial has `Y`-degree exactly two. -/
lemma weierstrass_natDegree (a b : k) : (weierstrass a b).natDegree = 2 := by
  unfold weierstrass; compute_degree!

/-- No polynomial in `X` can be a root of the Weierstrass polynomial, by
degree-counting: `X³ + aX + b` has odd degree and so is not a square. -/
lemma weierstrass_no_root (a b : k) (g : Polynomial k) :
    ¬(weierstrass a b).IsRoot g := by
  unfold weierstrass
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  intro h
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X +
      Polynomial.C b : Polynomial k).natDegree = 3 := by
    compute_degree!
  rw [← h] at hdeg
  have hg_ne : g ≠ 0 := by intro hg0; subst hg0; simp at hdeg
  rw [Polynomial.natDegree_pow g 2] at hdeg
  omega

/-- The Weierstrass polynomial is irreducible in `k[X][Y]`, hence the cubic
defines an integral plane curve. -/
theorem weierstrass_irreducible (a b : k) : Irreducible (weierstrass a b) := by
  have hm := weierstrass_monic a b
  have h2 : 2 ≤ (weierstrass a b).natDegree := by rw [weierstrass_natDegree]
  have h3 : (weierstrass a b).natDegree ≤ 3 := by rw [weierstrass_natDegree]; norm_num
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three h2 h3,
      Multiset.eq_zero_iff_forall_notMem]
  intro x
  rw [Polynomial.mem_roots hm.ne_zero]
  exact weierstrass_no_root a b x

/-- Alternative proof of irreducibility, via the mathlib affine Weierstrass API. -/
theorem weierstrass_irreducible_via_mathlib (a b : k) : Irreducible (weierstrass a b) := by
  rw [weierstrass_eq_polynomial]
  exact WeierstrassCurve.Affine.irreducible_polynomial

/-- The coordinate ring `k[X][Y]/(Y² − X³ − aX − b)` of the affine Weierstrass
curve is an integral domain. -/
noncomputable instance weierstrass_coordinate_ring_isDomain (a b : k) :
    IsDomain (AdjoinRoot (weierstrass a b)) :=
  AdjoinRoot.isDomain_of_prime (Irreducible.prime (weierstrass_irreducible a b))

/-- Ring equivalence between our coordinate ring and the mathlib affine
coordinate ring, transporting via `weierstrass_eq_polynomial`. -/
noncomputable def coordinateRingEquiv (a b : k) :
    AdjoinRoot (weierstrass a b) ≃+*
      AdjoinRoot (shortWeierstrass a b).toAffine.polynomial :=
  RingEquiv.cast (by rw [weierstrass_eq_polynomial])

/-- Discriminant of the short Weierstrass curve: `Δ = −16·(4a³ + 27b²)`. -/
lemma shortWeierstrass_disc (a b : k) :
    (shortWeierstrass a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp [shortWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- In characteristic `≠ 2`, the discriminant is non-zero iff `4a³ + 27b² ≠ 0`. -/
lemma shortWeierstrass_disc_ne_zero (a b : k)
    (hchar2 : (2 : k) ≠ 0) (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    (shortWeierstrass a b).Δ ≠ 0 := by
  rw [shortWeierstrass_disc]
  have h16 : (16 : k) ≠ 0 := by
    intro h
    apply hchar2
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this] at h
    exact pow_eq_zero_iff (by norm_num : 4 ≠ 0) |>.mp h
  exact mul_ne_zero (neg_ne_zero.mpr h16) hdisc

/-- A point `(x₀, y₀)` lies on the short Weierstrass curve iff
`y₀² = x₀³ + a x₀ + b`. -/
lemma shortWeierstrass_equation_iff (a b x₀ y₀ : k) :
    (shortWeierstrass a b).toAffine.Equation x₀ y₀ ↔
      y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [shortWeierstrass]

/-- Smoothness via the Jacobian criterion: at any point on the curve, the two
partial derivatives `2y` and `3x² + a` cannot vanish simultaneously when the
discriminant is non-zero. -/
theorem weierstrass_jacobian_smooth (a b : k)
    (hchar2 : (2 : k) ≠ 0)
    (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (x₀ y₀ : k)
    (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b)
    : ¬(2 * y₀ = 0 ∧ 3 * x₀ ^ 2 + a = 0) := by
  intro ⟨hy, hx⟩

  have hy0 : y₀ = 0 := (mul_eq_zero.mp hy).resolve_left hchar2

  rw [hy0, zero_pow (by norm_num : 2 ≠ 0)] at hcurve

  have ha : a = -(3 * x₀ ^ 2) := by linear_combination hx

  have hb : b = 2 * x₀ ^ 3 := by rw [ha] at hcurve; linear_combination -hcurve

  exact hdisc (by rw [ha, hb]; ring)

/-- Equivalent formulation of the Jacobian smoothness criterion: at any curve
point, at least one of the two partial derivatives is non-zero. -/
theorem weierstrass_smooth_at_point (a b : k)
    (hchar2 : (2 : k) ≠ 0)
    (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (x₀ y₀ : k)
    (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b)
    : 2 * y₀ ≠ 0 ∨ 3 * x₀ ^ 2 + a ≠ 0 := by
  by_contra h
  push Not at h
  exact weierstrass_jacobian_smooth a b hchar2 hdisc x₀ y₀ hcurve ⟨h.1, h.2⟩

/-- Smoothness of the elliptic curve: every point on the short Weierstrass
curve is nonsingular when `Δ ≠ 0` (i.e. `char k ≠ 2` and `4a³ + 27b² ≠ 0`). -/
theorem shortWeierstrass_nonsingular (a b : k)
    (hchar2 : (2 : k) ≠ 0) (hdisc : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (x₀ y₀ : k) (hcurve : y₀ ^ 2 = x₀ ^ 3 + a * x₀ + b) :
    (shortWeierstrass a b).toAffine.Nonsingular x₀ y₀ := by
  have heq : (shortWeierstrass a b).toAffine.Equation x₀ y₀ :=
    (shortWeierstrass_equation_iff a b x₀ y₀).mpr hcurve
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (shortWeierstrass_disc_ne_zero a b hchar2 hdisc)).mp heq

/-- Characterization of nonsingularity in terms of the defining equation and
the explicit Jacobian non-vanishing condition. -/
lemma shortWeierstrass_nonsingular_iff (a b x₀ y₀ : k) :
    (shortWeierstrass a b).toAffine.Nonsingular x₀ y₀ ↔
      (shortWeierstrass a b).toAffine.Equation x₀ y₀ ∧
        (-(3 * x₀ ^ 2 + a) ≠ 0 ∨ 2 * y₀ ≠ 0) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  simp [shortWeierstrass]

end EllipticCurveSmooth
