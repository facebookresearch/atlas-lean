/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.Hensel

noncomputable section

open Polynomial

section DoubleRoot

/-- Lemma 8.7: over any commutative ring $R$, an element $a \in R$ is a double root of
$f \in R[X]$ (i.e. $f(a) = 0$ and $f'(a) = 0$) if and only if $(X-a)^2$ divides $f$. -/
theorem double_root_iff_derivative_root {R : Type*} [CommRing R] (f : R[X]) (a : R) :
    (f.eval a = 0 ∧ (derivative f).eval a = 0) ↔ (X - C a) ^ 2 ∣ f := by
  constructor
  ·
    rintro ⟨hf, hf'⟩

    have h1 : (X - C a) ∣ f := dvd_iff_isRoot.mpr hf
    obtain ⟨q, hq⟩ := h1


    have hq_eval : q.eval a = 0 := by
      have key : (derivative f).eval a = q.eval a := by
        rw [hq, derivative_mul, eval_add, eval_mul, eval_mul,
            derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
            one_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
      rw [hf'] at key
      exact key.symm

    have h2 : (X - C a) ∣ q := dvd_iff_isRoot.mpr hq_eval

    obtain ⟨r, hr⟩ := h2
    exact ⟨r, by rw [hq, hr]; ring⟩
  ·
    rintro ⟨g, hg⟩
    constructor
    ·
      rw [hg, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
          zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    ·
      rw [hg, derivative_mul, derivative_pow]
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (by norm_num : (2 : ℕ) - 1 ≠ 0), derivative_sub, derivative_X, derivative_C,
        sub_zero]
      ring

end DoubleRoot

open PadicInt

/-- Definition 8.6 (formal derivative): for a polynomial $f \in R[X]$ over a commutative semiring,
the formal derivative $f'$ is the polynomial obtained term-by-term. Thin abbreviation for
`Polynomial.derivative`. -/
abbrev formalDerivative {R : Type*} [CommSemiring R] (f : R[X]) : R[X] :=
  Polynomial.derivative f

section FormalDerivativeProperties

variable {R : Type*} [CommSemiring R]


end FormalDerivativeProperties

variable {p : ℕ} [Fact p.Prime]

/-- If $x \in \mathbb{Z}_p$ is not divisible by $p$, then $\|x\| = 1$. Equivalently, $x$ is a unit
in $\mathbb{Z}_p$. -/
lemma PadicInt.norm_eq_one_of_not_dvd (x : ℤ_[p]) (h : ¬ (↑p ∣ x)) : ‖x‖ = 1 := by
  rw [← PadicInt.isUnit_iff]
  by_contra h'
  exact h ((PadicInt.norm_lt_one_iff_dvd x).mp (PadicInt.not_isUnit_iff.mp h'))

/-- Theorem 8.8 (Hensel's lemma, divisibility form): given $f \in \mathbb{Z}_p[X]$ and
$a \in \mathbb{Z}_p$ with $p \mid f(a)$ and $p \nmid f'(a)$, there exists a unique
$b \in \mathbb{Z}_p$ with $f(b) = 0$ and $p \mid (b - a)$. -/
theorem hensel_lemma (f : Polynomial ℤ_[p]) (a : ℤ_[p])
    (hfa : (↑p : ℤ_[p]) ∣ Polynomial.aeval a f)
    (hda : ¬ (↑p : ℤ_[p]) ∣ Polynomial.aeval a (Polynomial.derivative f)) :
    ∃! b : ℤ_[p], Polynomial.aeval b f = 0 ∧ (↑p : ℤ_[p]) ∣ (b - a) := by

  have hfa_norm : ‖Polynomial.aeval a f‖ < 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mpr hfa
  have hda_norm : ‖Polynomial.aeval a (Polynomial.derivative f)‖ = 1 :=
    PadicInt.norm_eq_one_of_not_dvd _ hda

  have hnorm : ‖Polynomial.aeval a f‖ <
      ‖Polynomial.aeval a (Polynomial.derivative f)‖ ^ 2 := by
    rw [hda_norm]; norm_num; exact hfa_norm

  obtain ⟨z, hz_root, hz_dist, _, hz_unique⟩ := hensels_lemma hnorm
  refine ⟨z, ⟨hz_root, ?_⟩, ?_⟩
  ·
    exact (PadicInt.norm_lt_one_iff_dvd _).mp (by rw [hda_norm] at hz_dist; exact hz_dist)
  ·
    intro y ⟨hy_root, hy_dvd⟩
    have hy_norm : ‖y - a‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr hy_dvd
    exact hz_unique y hy_root (by rw [hda_norm]; exact hy_norm)

/-- Theorem 8.8 (Hensel's lemma, norm form): given $f \in \mathbb{Z}_p[X]$ and
$a \in \mathbb{Z}_p$ with $\|f(a)\| < 1$ and $\|f'(a)\| = 1$, there exists a unique
$b \in \mathbb{Z}_p$ with $f(b) = 0$ and $\|b - a\| < 1$. -/
theorem hensel_lemma_norm (f : Polynomial ℤ_[p]) (a : ℤ_[p])
    (hfa : ‖Polynomial.aeval a f‖ < 1)
    (hda : ‖Polynomial.aeval a (Polynomial.derivative f)‖ = 1) :
    ∃! b : ℤ_[p], Polynomial.aeval b f = 0 ∧ ‖b - a‖ < 1 := by
  have hnorm : ‖Polynomial.aeval a f‖ <
      ‖Polynomial.aeval a (Polynomial.derivative f)‖ ^ 2 := by
    rw [hda]; norm_num; exact hfa
  obtain ⟨z, hz_root, hz_dist, _, hz_unique⟩ := hensels_lemma hnorm
  refine ⟨z, ⟨hz_root, by rw [hda] at hz_dist; exact hz_dist⟩, ?_⟩
  intro y ⟨hy_root, hy_close⟩
  exact hz_unique y hy_root (by rw [hda]; exact hy_close)

end
