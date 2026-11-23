/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

open Finset BigOperators
open scoped AddChar ComplexConjugate

namespace CharacterOrthogonality

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem orthogonality_group [DecidableEq G] (g₁ g₂ : G) :
    ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) =
      if g₁ = g₂ then (Fintype.card G : ℂ) else 0 := by

  have key : ∀ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) = χ (g₁ - g₂) := by
    intro χ
    rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv,
        ← AddChar.map_add_eq_mul, sub_eq_add_neg]

  simp_rw [key, AddChar.sum_apply_eq_ite, sub_eq_zero]

theorem orthogonality_group_normalized [DecidableEq G] (g₁ g₂ : G) :
    ((Fintype.card G : ℂ)⁻¹) * ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) =
      if g₁ = g₂ then 1 else 0 := by
  rw [orthogonality_group]
  split_ifs <;> simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

theorem orthogonality_char (χ₁ χ₂ : AddChar G ℂ) :
    ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) =
      if χ₁ = χ₂ then (Fintype.card G : ℂ) else 0 := by

  have key : ∀ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) = (χ₁ - χ₂) g := by
    intro g
    rw [AddChar.sub_apply, ← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv]

  simp_rw [key]
  classical
  rw [AddChar.sum_eq_ite]
  simp only [sub_eq_zero]

theorem orthogonality_char_normalized (χ₁ χ₂ : AddChar G ℂ) :
    ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) =
      if χ₁ = χ₂ then 1 else 0 := by
  rw [orthogonality_char]
  split_ifs <;> simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

theorem character_orthogonality_relations [DecidableEq G] :
    (∀ g₁ g₂ : G, ((Fintype.card G : ℂ)⁻¹) * ∑ χ : AddChar G ℂ, χ g₁ * (starRingEnd ℂ) (χ g₂) =
      if g₁ = g₂ then 1 else 0) ∧
    (∀ χ₁ χ₂ : AddChar G ℂ, ((Fintype.card G : ℂ)⁻¹) * ∑ g : G, χ₁ g * (starRingEnd ℂ) (χ₂ g) =
      if χ₁ = χ₂ then 1 else 0) :=
  ⟨orthogonality_group_normalized, orthogonality_char_normalized⟩

end CharacterOrthogonality
