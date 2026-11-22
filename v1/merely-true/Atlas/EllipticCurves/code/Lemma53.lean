/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Algebra.Polynomial.Derivative
import Atlas.EllipticCurves.code.IsogenyKernels
import Atlas.EllipticCurves.code.Isogenies

open Polynomial

/-- Over a field in which `2 ≠ 0`, if `t` is nonzero and `(t^2)' = 0`, then `t' = 0`.
Used in characteristic-`p` arguments where vanishing of the derivative of a square
forces vanishing of the derivative of the base polynomial. -/
lemma Polynomial.derivative_eq_zero_of_sq {k : Type*} [Field k]
    (hp2 : (2 : k) ≠ 0) {t : k[X]} (ht : t ≠ 0)
    (h : derivative (t ^ 2) = 0) : derivative t = 0 := by
  have h1 : C 2 * t * derivative t = 0 := by
    have h2 : derivative (t ^ 2) = C 2 * t * derivative t := by
      rw [derivative_pow]; ring_nf
    rw [h2] at h; exact h
  have h2_ne : (C (2 : k) : k[X]) ≠ 0 := by rwa [Ne, C_eq_zero]
  rcases mul_eq_zero.mp h1 with h2 | h3
  · rcases mul_eq_zero.mp h2 with h4 | h5
    · exact absurd h4 h2_ne
    · exact absurd h5 ht
  · exact h3

/-- From the curve equation `v³ · s² · f₁ = t² · w` of an isogeny in standard form,
together with `v' = 0` and `w' = 0`, deduce that the Wronskian of `s² · f₁` and `t²`
vanishes. A key computation in the proof of Lemma 5.3. -/
lemma wronskian_from_curve_eq {k : Type*} [Field k] {v s t f₁ w : k[X]}
    (hv_ne : v ≠ 0)
    (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
    (hv' : derivative v = 0) (hw' : derivative w = 0) :
    (s ^ 2 * f₁).wronskian (t ^ 2) = 0 := by
  have hcurve2 : v ^ 3 * (s ^ 2 * f₁) = t ^ 2 * w := by linear_combination hcurve
  have lhs_d : derivative (v ^ 3 * (s ^ 2 * f₁)) = v ^ 3 * derivative (s ^ 2 * f₁) := by
    rw [derivative_mul, derivative_pow, hv']; ring
  have rhs_d : derivative (t ^ 2 * w) = derivative (t ^ 2) * w := by
    rw [derivative_mul, hw', mul_zero, add_zero]
  have h_diff : v ^ 3 * derivative (s ^ 2 * f₁) = derivative (t ^ 2) * w := by
    have h := congr_arg derivative hcurve2; rw [lhs_d, rhs_d] at h; exact h
  have key : v ^ 3 * (s ^ 2 * f₁ * derivative (t ^ 2) - derivative (s ^ 2 * f₁) * t ^ 2) = 0 := by
    linear_combination derivative (t ^ 2) * hcurve2 - t ^ 2 * h_diff
  simp only [wronskian]
  exact or_iff_not_imp_left.mp (mul_eq_zero.mp key) (pow_ne_zero _ hv_ne)

/-- The "x-coordinate" part of Lemma 5.3: in characteristic `p > 0`, if coprime
polynomials `u, v` satisfy `u'v - uv' = 0` (inseparability of `u/v`), then `u` and
`v` are both `p`-th powers, i.e. of the form `f(x^p)` and `g(x^p)`. This corresponds
to Lemma 5.1 applied to the `x`-coordinate of an inseparable isogeny. -/
theorem lemma_5_3_x {k : Type*} [Field k] {p : ℕ} [CharP k p] (hp : p ≠ 0)
    {u v : k[X]} (hcop : IsCoprime u v)
    (hinsep : derivative u * v - u * derivative v = 0) :
    ∃ (f g : k[X]), expand k p f = u ∧ expand k p g = v := by
  have hwronskian : u.wronskian v = 0 := by
    simp only [wronskian]; linear_combination -hinsep
  have ⟨hu', hv'⟩ := hcop.wronskian_eq_zero_iff.mp hwronskian
  exact ⟨contract p u, contract p v, expand_contract p hu' hp, expand_contract p hv' hp⟩

/-- If `s` and `t` are coprime and `f₁` and `t` are coprime, then `s² · f₁` is
coprime to `t²`. A bookkeeping lemma supporting the curve equation analysis. -/
theorem coprime_s2f1_t2 {k : Type*} [Field k] {s t f₁ : k[X]}
    (hcop_st : IsCoprime s t) (hcop_ft : IsCoprime f₁ t) :
    IsCoprime (s ^ 2 * f₁) (t ^ 2) :=
  (hcop_st.pow_left.pow_right).mul_left (hcop_ft.pow_right)

/-- If `a` is a unit in `k[X]` and `c ∣ a · b`, then `c ∣ b`. A small divisibility
lemma used to peel off unit constants in characteristic-`p` arguments. -/
lemma dvd_of_dvd_mul_isUnit_poly {k : Type*} [Field k] {a b c : k[X]}
    (hu : IsUnit a) (h : c ∣ a * b) : c ∣ b := by
  rcases h with ⟨d, hd⟩; rcases hu with ⟨u, rfl⟩
  exact ⟨↑u⁻¹ * d, by
    rw [show b = ↑u⁻¹ * (↑u * b) from by simp [Units.inv_mul_cancel_left], hd]; ring⟩

/-- If `f₁` is separable, `m > 0`, `m ≠ 0` in `k`, and `(r² · f₁^m)' = 0`, then
`f₁ ∣ r`. This is the inductive step extracting more `f₁` factors from `s` in the
proof of the `y`-coordinate part of Lemma 5.3. -/
lemma sep_dvd_of_deriv_sq_mul_pow {k : Type*} [Field k]
    {r f₁ : k[X]} {m : ℕ} (hm : m > 0) (hCm : (m : k) ≠ 0)
    (hf₁_sep : f₁.Separable) (h_deriv : derivative (r ^ 2 * f₁ ^ m) = 0) :
    f₁ ∣ r := by
  have hf₁_sf := hf₁_sep.squarefree
  have hf₁_ne := hf₁_sf.ne_zero
  have h1 : derivative (r ^ 2) * f₁ ^ m + r ^ 2 * derivative (f₁ ^ m) = 0 := by
    rw [← derivative_mul]; exact h_deriv
  rw [derivative_pow f₁ m] at h1
  have h2 : f₁ ^ (m - 1) * (derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁) = 0 := by
    have : f₁ ^ m = f₁ * f₁ ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this] at h1
    have eq : derivative (r ^ 2) * (f₁ * f₁ ^ (m - 1)) +
        r ^ 2 * (C (↑m : k) * f₁ ^ (m - 1) * derivative f₁) =
        f₁ ^ (m - 1) * (derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁) := by ring
    rw [eq] at h1; exact h1
  have h3 : derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁ = 0 :=
    or_iff_not_imp_left.mp (mul_eq_zero.mp h2) (pow_ne_zero _ hf₁_ne)
  have h4 : f₁ ∣ C (↑m : k) * r ^ 2 := hf₁_sep.dvd_of_dvd_mul_right (by
    rw [(neg_eq_of_add_eq_zero_right h3).symm]; exact dvd_neg.mpr (dvd_mul_left f₁ _))
  exact (hf₁_sf.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp
    (dvd_of_dvd_mul_isUnit_poly
      (by rw [Polynomial.isUnit_C, isUnit_iff_ne_zero]; exact hCm) h4)

/-- The "y-coordinate" factorization of Lemma 5.3: in characteristic `p > 0`, if
`f₁` is separable, `s ≠ 0`, and `(s² · f₁)' = 0`, then `s² · f₁ = (expand_p g₂)² · f₁^p`
for some `g₂`. This shows the `y`-coefficient of an inseparable isogeny is a
`p`-th power times the suitable factor of `f₁`. -/
theorem insep_y_factor {k : Type*} [Field k] {p : ℕ} [CharP k p]
    (hp : p ≠ 0) (hp2 : (2 : k) ≠ 0)
    {s f₁ : k[X]} (hs : s ≠ 0) (hf₁_sep : f₁.Separable)
    (h_deriv : derivative (s ^ 2 * f₁) = 0) :
    ∃ (g₂ : k[X]), s ^ 2 * f₁ = (expand k p g₂) ^ 2 * f₁ ^ p := by
  have hf₁_ne := hf₁_sep.squarefree.ne_zero
  have hp_prime : Nat.Prime p := by
    rcases CharP.char_is_prime_or_zero k p with h | h; exact h; exact absurd h hp
  have hp2n : p ≠ 2 := by intro h; subst h; exact hp2 (CharP.cast_eq_zero k 2)

  have key : ∀ n : ℕ, n ≤ (p - 1) / 2 →
      ∃ r : k[X], s = f₁ ^ n * r ∧
        derivative (r ^ 2 * f₁ ^ (2 * n + 1)) = 0 ∧ r ≠ 0 := by
    intro n hn
    induction n with
    | zero => exact ⟨s, by simp, by simpa using h_deriv, hs⟩
    | succ n ih =>
      obtain ⟨r, hrs, hrd, hr_ne⟩ := ih (le_of_lt (Nat.lt_of_succ_le hn))
      have h_lt : 2 * n + 1 < p := by
        have := Nat.lt_of_succ_le hn; omega
      obtain ⟨r', rfl⟩ := sep_dvd_of_deriv_sq_mul_pow (by omega) (by
        intro h; rw [CharP.cast_eq_zero_iff k p] at h
        exact Nat.not_dvd_of_pos_of_lt (by omega) h_lt h) hf₁_sep hrd
      refine ⟨r', by rw [hrs, pow_succ, mul_assoc], ?_,
        by intro h; apply hr_ne; rw [h, mul_zero]⟩
      rwa [show (f₁ * r') ^ 2 * f₁ ^ (2 * n + 1) =
        r' ^ 2 * f₁ ^ (2 * (n + 1) + 1) from by ring_nf] at hrd

  obtain ⟨r, hrs, hrd, hr_ne⟩ := key ((p - 1) / 2) le_rfl
  have h_exp : 2 * ((p - 1) / 2) + 1 = p := by
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hp_prime hp2n; omega
  rw [h_exp] at hrd

  have h_dr2_zero : derivative (r ^ 2) = 0 := by
    have h := hrd
    rw [derivative_mul, show derivative (f₁ ^ p) = 0 from by
      rw [derivative_pow]; simp,
      mul_zero, add_zero] at h
    exact or_iff_not_imp_right.mp (mul_eq_zero.mp h) (pow_ne_zero _ hf₁_ne)
  have hr'_zero := Polynomial.derivative_eq_zero_of_sq hp2 hr_ne h_dr2_zero
  refine ⟨contract p r, ?_⟩
  calc s ^ 2 * f₁
      = (f₁ ^ ((p - 1) / 2) * r) ^ 2 * f₁ := by rw [hrs]
    _ = r ^ 2 * f₁ ^ (2 * ((p - 1) / 2) + 1) := by ring
    _ = r ^ 2 * f₁ ^ p := by rw [h_exp]
    _ = (expand k p (contract p r)) ^ 2 * f₁ ^ p := by rw [expand_contract p hr'_zero hp]

/-- Auxiliary step toward Lemma 5.3: from the curve equation `v³ · s² · f₁ = t² · w`
together with `v' = w' = 0`, deduce that the `y`-denominator `t` has zero derivative.
This goes through the Wronskian vanishing and then `Polynomial.derivative_eq_zero_of_sq`. -/
theorem lemma_5_3_y_deriv_t {k : Type*} [Field k]
    (hp2 : (2 : k) ≠ 0)
    {v s t f₁ w : k[X]}
    (hv_ne : v ≠ 0) (ht_ne : t ≠ 0)
    (hcop_st : IsCoprime s t) (hcop_ft : IsCoprime f₁ t)
    (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
    (hv' : derivative v = 0) (hw' : derivative w = 0) :
    derivative t = 0 := by

  have hwron := wronskian_from_curve_eq hv_ne hcurve hv' hw'

  have hcop := coprime_s2f1_t2 hcop_st hcop_ft

  have ht2' := (hcop.wronskian_eq_zero_iff.mp hwron).2

  exact Polynomial.derivative_eq_zero_of_sq hp2 ht_ne ht2'

/-- Lemma 5.3 (Sutherland, Section 5.1): let `α : E₁ → E₂` be an inseparable
isogeny of elliptic curves `E₁: y² = f₁(x)`, `E₂: y² = f₂(x)` over a field `k` of
characteristic `p > 0`, written in standard form with `u/v` for the `x`-coordinate
and `s/t · y` for the `y`-coordinate. Then `u`, `v`, `t` are all `p`-th powers and
`s² · f₁` factors as `(p`-th power`)² · f₁^p`, so the inseparable isogeny factors
through Frobenius as `α = (a(x^p), b(x^p)·y^p)`. -/
theorem lemma_5_3 {k : Type*} [Field k] {p : ℕ} [CharP k p]
    (hp : p ≠ 0) (hp2 : (2 : k) ≠ 0)
    {u v s t f₁ w : k[X]}
    (hcop_uv : IsCoprime u v) (hcop_st : IsCoprime s t)
    (hcop_ft : IsCoprime f₁ t)
    (hv_ne : v ≠ 0) (ht_ne : t ≠ 0) (hs_ne : s ≠ 0)
    (hf₁_sep : f₁.Separable)
    (hinsep : derivative u * v - u * derivative v = 0)
    (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
    (hw' : derivative w = 0) :

    (∃ (f g : k[X]), expand k p f = u ∧ expand k p g = v) ∧

    (∃ (t₀ : k[X]), expand k p t₀ = t) ∧

    (∃ (g₂ : k[X]), s ^ 2 * f₁ = (expand k p g₂) ^ 2 * f₁ ^ p) := by

  have hwronskian : u.wronskian v = 0 := by
    simp only [wronskian]; linear_combination -hinsep
  have ⟨hu', hv'⟩ := hcop_uv.wronskian_eq_zero_iff.mp hwronskian
  refine ⟨⟨contract p u, contract p v, expand_contract p hu' hp, expand_contract p hv' hp⟩,
    ?_, ?_⟩

  · have ht' : derivative t = 0 :=
      lemma_5_3_y_deriv_t hp2 hv_ne ht_ne hcop_st hcop_ft hcurve hv' hw'
    exact ⟨contract p t, expand_contract p ht' hp⟩

  ·
    have hwron := wronskian_from_curve_eq hv_ne hcurve hv' hw'
    have hcop := coprime_s2f1_t2 hcop_st hcop_ft
    have hs2f1' := (hcop.wronskian_eq_zero_iff.mp hwron).1

    exact insep_y_factor hp hp2 hs_ne hf₁_sep hs2f1'
