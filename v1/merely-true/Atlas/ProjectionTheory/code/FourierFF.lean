/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Fintype.BigOperators

open Finset hiding card
open Fintype (card)
open scoped BigOperators

namespace FourierFF

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- The standard dot product on `F^d` packaged as an additive homomorphism in the
first argument: `x ↦ ∑ᵢ xᵢ ξᵢ`. -/
noncomputable def dotProd (ξ : Fin d → F) : (Fin d → F) →+ F where
  toFun x := ∑ i, x i * ξ i
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

/-- The Fourier character on `F^d` indexed by frequency `ξ`:
`x ↦ e(⟨x, ξ⟩)`, built from a base additive character `e` on `F`. -/
noncomputable def fourierChar (e : AddChar F ℂ) (ξ : Fin d → F) :
    AddChar (Fin d → F) ℂ :=
  e.compAddMonoidHom (dotProd ξ)

/-- Unfolds `fourierChar e ξ x` to the explicit formula `e(⟨x, ξ⟩) = e(∑ᵢ xᵢ ξᵢ)`. -/
@[simp]
lemma fourierChar_apply (e : AddChar F ℂ) (ξ x : Fin d → F) :
    fourierChar e ξ x = e (∑ i, x i * ξ i) := rfl

/-- Discrete Fourier transform of `f : F^d → ℂ` at frequency `ξ`:
$$\hat f(\xi) = \sum_{x \in F^d} f(x) \overline{e(\langle x, \xi\rangle)}.$$ -/
noncomputable def dft (e : AddChar F ℂ) (f : (Fin d → F) → ℂ)
    (ξ : Fin d → F) : ℂ :=
  ∑ x, f x * (fourierChar e ξ)⁻¹ x

/-- Rewrites the DFT in terms of `e(-⟨x, ξ⟩)` instead of the inverse character. -/
lemma dft_apply (e : AddChar F ℂ) (f : (Fin d → F) → ℂ)
    (ξ : Fin d → F) :
    dft e f ξ = ∑ x, f x * e (-(∑ i, x i * ξ i)) := by
  simp [dft, fourierChar, dotProd, AddChar.inv_apply]

/-- Nondegeneracy of the Fourier character: for a nontrivial base character `e`,
`fourierChar e a` is the trivial character iff `a = 0`. -/
lemma fourierChar_eq_zero_iff (e : AddChar F ℂ) (he : e ≠ 0) (a : Fin d → F) :
    fourierChar e a = 0 ↔ a = 0 := by
  have h01 : (0 : AddChar F ℂ) = 1 := by ext x; simp
  have he1 : e ≠ 1 := by rwa [← h01]
  have hprim := AddChar.IsPrimitive.of_ne_one he1
  constructor
  · intro h0
    rw [show (0 : AddChar (Fin d → F) ℂ) = 1 from by ext x; simp] at h0
    funext i
    have key : AddChar.mulShift e (a i) = 1 := by
      ext t
      have := DFunLike.ext_iff.mp h0 (fun j => if j = i then t else 0)
      simp only [fourierChar, AddChar.compAddMonoidHom_apply, dotProd,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddChar.one_apply] at this
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    by_contra hai
    exact (hprim hai) key
  · intro ha; subst ha; ext ξ; simp [fourierChar, dotProd]

/-- Orthogonality of characters on `F^d`:
$$\sum_{\xi \in F^d} e(\langle a, \xi\rangle) = \begin{cases} q^d & a = 0\\ 0 & a \neq 0.\end{cases}$$ -/
lemma sum_fourierChar (e : AddChar F ℂ) (he : e ≠ 0) (a : Fin d → F) :
    ∑ ξ, fourierChar e a ξ =
      if a = 0 then (card (Fin d → F) : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [fourierChar, dotProd]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr ((fourierChar_eq_zero_iff e he a).not.mpr ha)

/--
Theorem 2.5 (Fourier inversion on `F^d`). For any `f : F^d → ℂ` and any `x ∈ F^d`,
$$f(x) = \frac{1}{q^d} \sum_{\xi \in F^d} \hat f(\xi)\, e(\langle x, \xi\rangle).$$
Splitting the `ξ = 0` term yields the zero-frequency / high-frequency decomposition
$f = f_0 + f_h$ with $f_0 = \tfrac{1}{q^d}\hat f(0)$ constant.
-/
theorem fourier_inversion (e : AddChar F ℂ) (he : e ≠ 0)
    (f : (Fin d → F) → ℂ) (x : Fin d → F) :
    f x = (↑(card (Fin d → F)))⁻¹ *
      ∑ ξ, dft e f ξ * fourierChar e ξ x := by
  simp only [dft]

  have step1 : ∑ ξ, (∑ y, f y * (fourierChar e ξ)⁻¹ y) * fourierChar e ξ x =
      ∑ y, f y * (∑ ξ, (fourierChar e ξ)⁻¹ y * fourierChar e ξ x) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [step1]

  have step2 : ∀ y, ∑ ξ, (fourierChar e ξ)⁻¹ y * fourierChar e ξ x =
      ∑ ξ, fourierChar e ξ (x - y) := by
    intro y; congr 1; ext ξ
    simp only [fourierChar, AddChar.compAddMonoidHom_apply, AddChar.inv_apply,
      dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_neg]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
  simp_rw [step2]

  have step3 : ∀ y, ∑ ξ, fourierChar e ξ (x - y) = ∑ ξ, fourierChar e (x - y) ξ := by
    intro y; congr 1; ext ξ
    simp only [fourierChar, AddChar.compAddMonoidHom_apply, dotProd,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 1; apply Finset.sum_congr rfl; intros; ring
  simp_rw [step3]

  simp_rw [sum_fourierChar e he]

  simp only [sub_eq_zero, mul_ite, mul_zero, @eq_comm _ x]
  rw [Finset.sum_ite_eq' Finset.univ x]
  simp only [Finset.mem_univ, ite_true]
  have hcard : (card (Fin d → F) : ℂ) ≠ 0 := by
    have : 0 < card (Fin d → F) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

end FourierFF
