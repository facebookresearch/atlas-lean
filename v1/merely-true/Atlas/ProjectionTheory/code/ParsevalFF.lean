/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.FourierFF
import Mathlib.Analysis.RCLike.Basic

open Finset hiding card
open Fintype (card)
open scoped BigOperators ComplexConjugate

namespace FourierFF

variable {p : ℕ} [Fact (Nat.Prime p)] {d : ℕ}

/-- The complex conjugate of the discrete Fourier transform satisfies
$\overline{\hat g(\xi)} = \sum_y \overline{g(y)}\, e_\xi(y)$, swapping the additive
character for its complex conjugate. -/
lemma conj_dft (e : AddChar (ZMod p) ℂ) (g : (Fin d → ZMod p) → ℂ)
    (ξ : Fin d → ZMod p) :
    starRingEnd ℂ (dft e g ξ) = ∑ y, starRingEnd ℂ (g y) * fourierChar e ξ y := by
  simp only [dft]
  rw [map_sum]
  congr 1; ext y
  rw [map_mul]
  congr 1
  rw [AddChar.inv_apply, fourierChar_apply, fourierChar_apply]
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp [neg_mul, ← Finset.sum_neg_distrib]

/-- Multiplicative property of the Fourier character:
$e_\xi(x)^{-1} \cdot e_\xi(y) = e_\xi(y - x)$. -/
lemma inv_mul_fourierChar (e : AddChar (ZMod p) ℂ) (ξ x y : Fin d → ZMod p) :
    (fourierChar e ξ)⁻¹ x * fourierChar e ξ y = fourierChar e ξ (y - x) := by
  simp only [fourierChar, AddChar.compAddMonoidHom_apply, AddChar.inv_apply,
    dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_neg]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Symmetry of the Fourier character in its two arguments: $e_\xi(a) = e_a(\xi)$, a
consequence of the symmetric dot product $a \cdot \xi = \xi \cdot a$. -/
lemma fourierChar_swap (e : AddChar (ZMod p) ℂ) (a ξ : Fin d → ZMod p) :
    fourierChar e ξ a = fourierChar e a ξ := by
  simp only [fourierChar_apply]
  congr 1
  apply Finset.sum_congr rfl; intros; ring

/-- **Parseval/Plancherel on $\mathbb{F}_q^d$ (Theorem 2.6).** For
$f, g : \mathbb{F}_q^d \to \mathbb{C}$ and a non-trivial additive character `e`,
$$\sum_{x \in \mathbb{F}_q^d} f(x)\,\overline{g(x)}
   = \frac{1}{q^d}\, \sum_{\xi \in \mathbb{F}_q^d} \hat f(\xi)\, \overline{\hat g(\xi)}.$$ -/
theorem parseval (e : AddChar (ZMod p) ℂ) (he : e ≠ 0)
    (f g : (Fin d → ZMod p) → ℂ) :
    ∑ x, f x * starRingEnd ℂ (g x) =
      (↑(card (Fin d → ZMod p)))⁻¹ *
        ∑ ξ, dft e f ξ * starRingEnd ℂ (dft e g ξ) := by

  simp_rw [conj_dft]
  simp only [dft]

  have key : ∀ x y : Fin d → ZMod p,
      ∑ ξ, (fourierChar e ξ)⁻¹ x * fourierChar e ξ y =
        if y = x then (card (Fin d → ZMod p) : ℂ) else 0 := by
    intro x y
    simp_rw [inv_mul_fourierChar, fourierChar_swap e (y - x)]
    rw [sum_fourierChar e he]
    simp [sub_eq_zero]

  have expand_rhs :
    (↑(card (Fin d → ZMod p)))⁻¹ *
      ∑ ξ : Fin d → ZMod p, (∑ x, f x * (fourierChar e ξ)⁻¹ x) *
        (∑ y, starRingEnd ℂ (g y) * fourierChar e ξ y) =
    (↑(card (Fin d → ZMod p)))⁻¹ *
      ∑ x, ∑ y, f x * starRingEnd ℂ (g y) *
        (∑ ξ, (fourierChar e ξ)⁻¹ x * fourierChar e ξ y) := by
    congr 1
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext x
    rw [Finset.sum_comm]
    congr 1; ext y
    congr 1; ext ξ
    ring
  rw [expand_rhs]

  simp_rw [key]
  simp only [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]

  have hcard : (card (Fin d → ZMod p) : ℂ) ≠ 0 := by
    rw [Fintype.card_pi_const, ZMod.card]
    exact_mod_cast pow_ne_zero d (Nat.Prime.ne_zero (Fact.out))
  rw [Finset.mul_sum]
  congr 1; ext x
  field_simp

end FourierFF
