/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

namespace Lemma2417

/-- If $p^m \mid a$ and $p^n \mid b$ in $\mathbb{Z}_p$, then $p^{m+n} \mid a \cdot b$. -/
lemma dvd_mul_of_pow_dvd {a b : ℤ_[p]} {m n : ℕ}
    (ha : (p : ℤ_[p]) ^ m ∣ a) (hb : (p : ℤ_[p]) ^ n ∣ b) :
    (p : ℤ_[p]) ^ (m + n) ∣ a * b := by
  obtain ⟨u, rfl⟩ := ha; obtain ⟨v, rfl⟩ := hb; exact ⟨u * v, by ring⟩

/-- Any element of $\mathbb{Z}_p$ divisible by $p$ has norm strictly less than $1$. -/
lemma padic_norm_lt_one_of_dvd_p (x : ℤ_[p]) (hx : (p : ℤ_[p]) ∣ x) : ‖x‖ < 1 := by
  obtain ⟨c, rfl⟩ := hx
  calc ‖(p : ℤ_[p]) * c‖ = ‖(p : ℤ_[p])‖ * ‖c‖ := norm_mul _ _
    _ ≤ ‖(p : ℤ_[p])‖ := mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one c)
    _ = (p : ℝ)⁻¹ := PadicInt.norm_p
    _ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.Prime.one_lt hp.out)

/-- If $x \in \mathbb{Z}_p$ is divisible by $p$, then $1 + x$ is a unit (by the ultrametric
inequality, $\|1 + x\| = 1$). -/
lemma padic_isUnit_one_add (x : ℤ_[p]) (hx : (p : ℤ_[p]) ∣ x) : IsUnit (1 + x) := by
  rw [PadicInt.isUnit_iff]
  have hxlt : ‖x‖ < 1 := padic_norm_lt_one_of_dvd_p x hx
  have hne : ‖(1 : ℤ_[p])‖ ≠ ‖x‖ := by simp only [norm_one]; exact ne_of_gt hxlt
  rw [PadicInt.norm_add_eq_max_of_ne hne, norm_one, max_eq_left (le_of_lt hxlt)]

/-- The condition that a (projective-like) point $(x, z)$ on the dehomogenized Weierstrass curve
$z = x^3 + a_4 x z^2 + a_6 z^3$ lies in the $n$-th piece $E_n$ of the $p$-adic filtration:
$p^n \mid x$ and $p^{3n} \mid z$. -/
structure IsInEn (a₄ a₆ : ℤ_[p]) (n : ℕ) (x z : ℤ_[p]) : Prop where
  on_curve : z = x ^ 3 + a₄ * x * z ^ 2 + a₆ * z ^ 3
  val_x : (p : ℤ_[p]) ^ n ∣ x
  val_z : (p : ℤ_[p]) ^ (3 * n) ∣ z

/-- Factorization of the difference of two cubic evaluations: $f(a) - f(b) = (a - b) \cdot q(a, b)$
where $q$ is symmetric in $a, b$. -/
lemma cubic_diff_factor {R : Type*} [CommRing R] (c₃ c₂ c₁ : R) (a b : R) :
    c₃ * a ^ 3 + c₂ * a ^ 2 + c₁ * a - (c₃ * b ^ 3 + c₂ * b ^ 2 + c₁ * b) =
    (a - b) * (c₃ * (a ^ 2 + a * b + b ^ 2) + c₂ * (a + b) + c₁) := by ring

/-- **Vieta's formula (distinct roots case).** If $x_1, x_2, x_3$ are three distinct roots of a
cubic $c_3 X^3 + c_2 X^2 + c_1 X + c_0$ in a domain, then $c_3 (x_1 + x_2 + x_3) + c_2 = 0$. -/
lemma vieta_sum_distinct {R : Type*} [CommRing R] [IsDomain R]
    (c₃ c₂ c₁ c₀ x₁ x₂ x₃ : R)
    (h1 : c₃ * x₁ ^ 3 + c₂ * x₁ ^ 2 + c₁ * x₁ + c₀ = 0)
    (h2 : c₃ * x₂ ^ 3 + c₂ * x₂ ^ 2 + c₁ * x₂ + c₀ = 0)
    (h3 : c₃ * x₃ ^ 3 + c₂ * x₃ ^ 2 + c₁ * x₃ + c₀ = 0)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    c₃ * (x₁ + x₂ + x₃) + c₂ = 0 := by
  have sub12 : c₃ * x₁ ^ 3 + c₂ * x₁ ^ 2 + c₁ * x₁ -
      (c₃ * x₂ ^ 3 + c₂ * x₂ ^ 2 + c₁ * x₂) = 0 := by linear_combination h1 - h2
  rw [cubic_diff_factor] at sub12
  have eq12 : c₃ * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + c₂ * (x₁ + x₂) + c₁ = 0 :=
    (mul_eq_zero.mp sub12).resolve_left (sub_ne_zero.mpr h12)
  have sub13 : c₃ * x₁ ^ 3 + c₂ * x₁ ^ 2 + c₁ * x₁ -
      (c₃ * x₃ ^ 3 + c₂ * x₃ ^ 2 + c₁ * x₃) = 0 := by linear_combination h1 - h3
  rw [cubic_diff_factor] at sub13
  have eq13 : c₃ * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) + c₂ * (x₁ + x₃) + c₁ = 0 :=
    (mul_eq_zero.mp sub13).resolve_left (sub_ne_zero.mpr h13)
  have factored : (x₂ - x₃) * (c₃ * (x₁ + x₂ + x₃) + c₂) = 0 := by
    linear_combination eq12 - eq13
  exact (mul_eq_zero.mp factored).resolve_left (sub_ne_zero.mpr h23)

/-- Substituting the line $z = \alpha x + \beta$ into the Weierstrass equation
$z = x^3 + a_4 x z^2 + a_6 z^3$ yields a cubic in $x$ with explicit coefficients. -/
lemma cubic_from_curve_and_line {R : Type*} [CommRing R]
    (a₄ a₆ α β x z : R)
    (hcurve : z = x ^ 3 + a₄ * x * z ^ 2 + a₆ * z ^ 3)
    (hline : z = α * x + β) :
    (1 + a₄ * α ^ 2 + a₆ * α ^ 3) * x ^ 3 +
    (2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) * x ^ 2 +
    (a₄ * β ^ 2 + 3 * a₆ * α * β ^ 2 - α) * x +
    (a₆ * β ^ 3 - β) = 0 := by
  rw [hline] at hcurve; linear_combination -hcurve

/-- Vieta's formula applied to three distinct collinear points on the Weierstrass curve:
the sum of the $x$-coordinates satisfies $(1 + a_4 \alpha^2 + a_6 \alpha^3)(x_1 + x_2 + x_3) +
(2 a_4 \alpha \beta + 3 a_6 \alpha^2 \beta) = 0$. -/
lemma vieta_from_curve_distinct
    (a₄ a₆ α β : ℤ_[p]) (x₁ x₂ x₃ z₁ z₂ z₃ : ℤ_[p])
    (hcurve1 : z₁ = x₁ ^ 3 + a₄ * x₁ * z₁ ^ 2 + a₆ * z₁ ^ 3)
    (hcurve2 : z₂ = x₂ ^ 3 + a₄ * x₂ * z₂ ^ 2 + a₆ * z₂ ^ 3)
    (hcurve3 : z₃ = x₃ ^ 3 + a₄ * x₃ * z₃ ^ 2 + a₆ * z₃ ^ 3)
    (hline1 : z₁ = α * x₁ + β)
    (hline2 : z₂ = α * x₂ + β)
    (hline3 : z₃ = α * x₃ + β)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    (1 + a₄ * α ^ 2 + a₆ * α ^ 3) * (x₁ + x₂ + x₃) +
    (2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) = 0 := by
  have h1 := cubic_from_curve_and_line a₄ a₆ α β x₁ z₁ hcurve1 hline1
  have h2 := cubic_from_curve_and_line a₄ a₆ α β x₂ z₂ hcurve2 hline2
  have h3 := cubic_from_curve_and_line a₄ a₆ α β x₃ z₃ hcurve3 hline3
  exact vieta_sum_distinct _ _ _ _ _ _ _ h1 h2 h3 h12 h13 h23

/-- Algebraic identity relating the differences $z_2 - z_1$ and $x_2 - x_1$ for two points on the
Weierstrass curve, before cancelling $x_2 - x_1$. -/
lemma slope_identity_precancellation {R : Type*} [CommRing R]
    (a₄ a₆ x₁ x₂ z₁ z₂ : R)
    (hcurve1 : z₁ = x₁ ^ 3 + a₄ * x₁ * z₁ ^ 2 + a₆ * z₁ ^ 3)
    (hcurve2 : z₂ = x₂ ^ 3 + a₄ * x₂ * z₂ ^ 2 + a₆ * z₂ ^ 3) :
    (z₂ - z₁) * (1 - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)) =
    (x₂ - x₁) * (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 + a₄ * z₂ ^ 2) := by
  linear_combination hcurve2 - hcurve1

/-- Identity expressing the slope $\alpha$ of a chord through two distinct points on the
Weierstrass curve: $\alpha \cdot D = N$, where $D$ is the slope denominator and $N$ is the
numerator. -/
lemma slope_identity
    (a₄ a₆ α β x₁ x₂ z₁ z₂ : ℤ_[p])
    (hcurve1 : z₁ = x₁ ^ 3 + a₄ * x₁ * z₁ ^ 2 + a₆ * z₁ ^ 3)
    (hcurve2 : z₂ = x₂ ^ 3 + a₄ * x₂ * z₂ ^ 2 + a₆ * z₂ ^ 3)
    (hline1 : z₁ = α * x₁ + β) (hline2 : z₂ = α * x₂ + β)
    (hne : x₁ ≠ x₂) :
    α * (1 - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)) =
    (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 + a₄ * z₂ ^ 2) := by
  have hpre := slope_identity_precancellation a₄ a₆ x₁ x₂ z₁ z₂ hcurve1 hcurve2
  have hzdiff : z₂ - z₁ = α * (x₂ - x₁) := by linear_combination hline2 - hline1
  rw [hzdiff] at hpre
  rw [show α * (x₂ - x₁) * (1 - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)) =
    (x₂ - x₁) * (α * (1 - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)))
    from by ring] at hpre
  exact mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)) hpre

/-- The slope denominator $D = 1 - a_4 x_1 (z_2 + z_1) - a_6 (z_2^2 + z_1 z_2 + z_1^2)$ is a
$p$-adic unit when $x_1, z_1, z_2$ lie in the filtration $E_n$ (since $D$ is $1$ plus a
multiple of $p$). -/
lemma slope_denom_isUnit
    (a₄ a₆ x₁ z₁ z₂ : ℤ_[p]) (n : ℕ) (hn : 0 < n)
    (hx1 : (p : ℤ_[p]) ^ n ∣ x₁)
    (hz1 : (p : ℤ_[p]) ^ (3 * n) ∣ z₁) (hz2 : (p : ℤ_[p]) ^ (3 * n) ∣ z₂) :
    IsUnit (1 - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)) := by

  have hx1p : (p : ℤ_[p]) ∣ x₁ := dvd_trans (dvd_pow_self _ (by omega : n ≠ 0)) hx1
  have hz1p : (p : ℤ_[p]) ∣ z₁ := dvd_trans (dvd_pow_self _ (by omega : 3 * n ≠ 0)) hz1
  have hz2p : (p : ℤ_[p]) ∣ z₂ := dvd_trans (dvd_pow_self _ (by omega : 3 * n ≠ 0)) hz2
  have hrem : (p : ℤ_[p]) ∣ (a₄ * x₁ * (z₂ + z₁) + a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2)) := by
    apply dvd_add
    · rw [show a₄ * x₁ * (z₂ + z₁) = x₁ * (a₄ * (z₂ + z₁)) from by ring]
      exact dvd_mul_of_dvd_left hx1p _
    · apply dvd_mul_of_dvd_right
      apply dvd_add; apply dvd_add
      · rw [sq]; exact dvd_mul_of_dvd_left hz2p _
      · exact dvd_mul_of_dvd_left hz1p _
      · rw [sq]; exact dvd_mul_of_dvd_left hz1p _

  rw [show (1 : ℤ_[p]) - a₄ * x₁ * (z₂ + z₁) - a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2) =
    1 + (-(a₄ * x₁ * (z₂ + z₁) + a₆ * (z₂ ^ 2 + z₁ * z₂ + z₁ ^ 2))) from by ring]
  exact padic_isUnit_one_add _ (dvd_neg.mpr hrem)

/-- The slope numerator $N = x_2^2 + x_1 x_2 + x_1^2 + a_4 z_2^2$ is divisible by $p^{2n}$ when
$x_1, x_2$ lie in $p^n \mathbb{Z}_p$ and $z_2$ lies in $p^{3n} \mathbb{Z}_p$. -/
lemma slope_numer_dvd
    (a₄ x₁ x₂ z₂ : ℤ_[p]) (n : ℕ)
    (hx1 : (p : ℤ_[p]) ^ n ∣ x₁) (hx2 : (p : ℤ_[p]) ^ n ∣ x₂)
    (hz2 : (p : ℤ_[p]) ^ (3 * n) ∣ z₂) :
    (p : ℤ_[p]) ^ (2 * n) ∣ (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 + a₄ * z₂ ^ 2) := by
  apply dvd_add; apply dvd_add; apply dvd_add
  · rw [sq, show (2 : ℕ) * n = n + n from by ring]
    exact dvd_mul_of_pow_dvd hx2 hx2
  · rw [show (2 : ℕ) * n = n + n from by ring]
    exact dvd_mul_of_pow_dvd hx1 hx2
  · rw [sq, show (2 : ℕ) * n = n + n from by ring]
    exact dvd_mul_of_pow_dvd hx1 hx1
  · apply dvd_mul_of_dvd_right
    apply dvd_trans (pow_dvd_pow _ (show 2 * n ≤ 6 * n by omega))
    rw [sq, show (6 : ℕ) * n = 3 * n + 3 * n from by ring]
    exact dvd_mul_of_pow_dvd hz2 hz2

/-- If two distinct points in the filtration $E_n$ lie on a line $z = \alpha x + \beta$, then
$p^{2n}$ divides the slope $\alpha$ (chord case). -/
lemma slope_in_p2n
    (a₄ a₆ α β x₁ x₂ z₁ z₂ : ℤ_[p]) (n : ℕ) (hn : 0 < n)
    (hcurve1 : z₁ = x₁ ^ 3 + a₄ * x₁ * z₁ ^ 2 + a₆ * z₁ ^ 3)
    (hcurve2 : z₂ = x₂ ^ 3 + a₄ * x₂ * z₂ ^ 2 + a₆ * z₂ ^ 3)
    (hline1 : z₁ = α * x₁ + β) (hline2 : z₂ = α * x₂ + β)
    (hne : x₁ ≠ x₂)
    (hx1 : (p : ℤ_[p]) ^ n ∣ x₁) (hx2 : (p : ℤ_[p]) ^ n ∣ x₂)
    (hz1 : (p : ℤ_[p]) ^ (3 * n) ∣ z₁) (hz2 : (p : ℤ_[p]) ^ (3 * n) ∣ z₂) :
    (p : ℤ_[p]) ^ (2 * n) ∣ α := by

  have hid := slope_identity a₄ a₆ α β x₁ x₂ z₁ z₂ hcurve1 hcurve2 hline1 hline2 hne

  have hDunit := slope_denom_isUnit a₄ a₆ x₁ z₁ z₂ n hn hx1 hz1 hz2

  have hNdvd := slope_numer_dvd a₄ x₁ x₂ z₂ n hx1 hx2 hz2

  obtain ⟨u, hu⟩ := hDunit
  rw [← hu, show α * ↑u = ↑u * α from mul_comm _ _] at hid
  rw [← hid] at hNdvd
  rwa [Units.dvd_mul_left] at hNdvd

/-- Given a line $z_1 = \alpha x_1 + \beta$ through a point in $E_n$, if $p^{2n} \mid \alpha$
then $p^{3n} \mid \beta$ (the intercept lies in $p^{3n} \mathbb{Z}_p$). -/
lemma intercept_in_p3n
    (α β x₁ z₁ : ℤ_[p]) (n : ℕ)
    (hline1 : z₁ = α * x₁ + β)
    (hx1 : (p : ℤ_[p]) ^ n ∣ x₁)
    (hz1 : (p : ℤ_[p]) ^ (3 * n) ∣ z₁)
    (hα : (p : ℤ_[p]) ^ (2 * n) ∣ α) :
    (p : ℤ_[p]) ^ (3 * n) ∣ β := by

  have hβ : β = z₁ - α * x₁ := by linear_combination -hline1
  rw [hβ]
  apply dvd_sub hz1
  rw [show (3 : ℕ) * n = 2 * n + n from by ring]
  exact dvd_mul_of_pow_dvd hα hx1

/-- From Vieta's relation $(1 + a_4 \alpha^2 + a_6 \alpha^3)(x_1 + x_2 + x_3) +
(2 a_4 \alpha \beta + 3 a_6 \alpha^2 \beta) = 0$, together with $p^{2n} \mid \alpha$ and
$p^{3n} \mid \beta$, conclude $p^{5n} \mid x_1 + x_2 + x_3$. -/
lemma valuation_from_vieta
    (a₄ a₆ α β x₁ x₂ x₃ : ℤ_[p]) (n : ℕ) (hn : 0 < n)
    (hvieta : (1 + a₄ * α ^ 2 + a₆ * α ^ 3) * (x₁ + x₂ + x₃) +
              (2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) = 0)
    (hα : (p : ℤ_[p]) ^ (2 * n) ∣ α)
    (hβ : (p : ℤ_[p]) ^ (3 * n) ∣ β) :
    (p : ℤ_[p]) ^ (5 * n) ∣ (x₁ + x₂ + x₃) := by

  have hα_p : (p : ℤ_[p]) ∣ α := dvd_trans (dvd_pow_self _ (by omega)) hα
  have hrem_dvd : (p : ℤ_[p]) ∣ (a₄ * α ^ 2 + a₆ * α ^ 3) :=
    dvd_add (dvd_mul_of_dvd_right (dvd_pow hα_p (by norm_num)) _)
            (dvd_mul_of_dvd_right (dvd_pow hα_p (by norm_num)) _)
  have hunit : IsUnit (1 + a₄ * α ^ 2 + a₆ * α ^ 3) := by
    rw [show 1 + a₄ * α ^ 2 + a₆ * α ^ 3 = 1 + (a₄ * α ^ 2 + a₆ * α ^ 3) from by ring]
    exact padic_isUnit_one_add _ hrem_dvd

  have hnum1 : (p : ℤ_[p]) ^ (5 * n) ∣ (2 * a₄ * α * β) := by
    rw [show 2 * a₄ * α * β = (2 * a₄) * (α * β) from by ring]
    apply dvd_mul_of_dvd_right
    rw [show (5 : ℕ) * n = 2 * n + 3 * n from by ring]
    exact dvd_mul_of_pow_dvd hα hβ
  have hnum2 : (p : ℤ_[p]) ^ (5 * n) ∣ (3 * a₆ * α ^ 2 * β) := by
    rw [show 3 * a₆ * α ^ 2 * β = (3 * a₆) * (α ^ 2 * β) from by ring]
    apply dvd_mul_of_dvd_right
    apply dvd_trans (pow_dvd_pow _ (show 5 * n ≤ 7 * n by omega))
    rw [show (7 : ℕ) * n = 4 * n + 3 * n from by ring]
    exact dvd_mul_of_pow_dvd
      (by rw [sq, show (4 : ℕ) * n = 2 * n + 2 * n from by ring]; exact dvd_mul_of_pow_dvd hα hα)
      hβ
  have hnum : (p : ℤ_[p]) ^ (5 * n) ∣ (2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) :=
    dvd_add hnum1 hnum2

  have hprod : (1 + a₄ * α ^ 2 + a₆ * α ^ 3) * (x₁ + x₂ + x₃) =
    -(2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) := by linear_combination hvieta

  obtain ⟨u, hu⟩ := hunit
  have hny : (p : ℤ_[p]) ^ (5 * n) ∣ -(2 * a₄ * α * β + 3 * a₆ * α ^ 2 * β) :=
    dvd_neg.mpr hnum
  rw [← hprod, ← hu] at hny
  rwa [Units.dvd_mul_left] at hny

/-- **Lemma 24.17 (distinct collinear points case).** Three distinct collinear points
$P_1, P_2, P_3$ in the filtration $E_n$ of the Weierstrass curve satisfy
$p^{5n} \mid x_1 + x_2 + x_3$. -/
theorem lemma_24_17_from_En
    (a₄ a₆ α β : ℤ_[p]) (x₁ x₂ x₃ z₁ z₂ z₃ : ℤ_[p]) (n : ℕ) (hn : 0 < n)
    (hP1 : IsInEn a₄ a₆ n x₁ z₁)
    (hP2 : IsInEn a₄ a₆ n x₂ z₂)
    (hP3 : IsInEn a₄ a₆ n x₃ z₃)
    (hline1 : z₁ = α * x₁ + β)
    (hline2 : z₂ = α * x₂ + β)
    (hline3 : z₃ = α * x₃ + β)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    (p : ℤ_[p]) ^ (5 * n) ∣ (x₁ + x₂ + x₃) := by

  have hcurve1 := hP1.on_curve
  have hcurve2 := hP2.on_curve
  have hcurve3 := hP3.on_curve

  have hα : (p : ℤ_[p]) ^ (2 * n) ∣ α :=
    slope_in_p2n a₄ a₆ α β x₁ x₂ z₁ z₂ n hn hcurve1 hcurve2 hline1 hline2 h12
      hP1.val_x hP2.val_x hP1.val_z hP2.val_z

  have hβ : (p : ℤ_[p]) ^ (3 * n) ∣ β :=
    intercept_in_p3n α β x₁ z₁ n hline1 hP1.val_x hP1.val_z hα

  have hvieta := vieta_from_curve_distinct a₄ a₆ α β x₁ x₂ x₃ z₁ z₂ z₃
    hcurve1 hcurve2 hcurve3 hline1 hline2 hline3 h12 h13 h23

  exact valuation_from_vieta a₄ a₆ α β x₁ x₂ x₃ n hn hvieta hα hβ

/-- Three points $(x_1, z_1), (x_2, z_2), (x_3, z_3) \in \mathbb{Z}_p^2$ are collinear if they
lie on a common line $z = \alpha x + \beta$ for some $\alpha, \beta \in \mathbb{Z}_p$. -/
def AreCollinear (x₁ z₁ x₂ z₂ x₃ z₃ : ℤ_[p]) : Prop :=
  ∃ α β : ℤ_[p], z₁ = α * x₁ + β ∧ z₂ = α * x₂ + β ∧ z₃ = α * x₃ + β





end Lemma2417
