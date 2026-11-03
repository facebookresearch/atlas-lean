/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finite.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Setoid.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.KrullDimension.Basic

open MvPolynomial

def projectiveEquiv (n : ℕ) : Setoid { v : Fin n → ℚ // v ≠ 0 } where
  r v w := ∃ (c : ℚ), c ≠ 0 ∧ v.val = c • w.val
  iseqv := {
    refl := fun v => ⟨1, one_ne_zero, by simp⟩
    symm := fun {v w} ⟨c, hc, hvw⟩ => ⟨c⁻¹, inv_ne_zero hc, by
      have h := congr_fun hvw
      ext i; simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
      rw [h i, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]⟩
    trans := fun {u v w} ⟨c₁, hc₁, huv⟩ ⟨c₂, hc₂, hvw⟩ =>
      ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, by
        have h1 := congr_fun huv
        have h2 := congr_fun hvw
        ext i; simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
        rw [h1 i, h2 i, mul_assoc]⟩
  }

def ProjectiveSpace (n : ℕ) := Quotient (projectiveEquiv n)

def projectiveRatPoints (n : ℕ) (eqs : Set (MvPolynomial (Fin n) ℚ)) : Type :=
  { p : ProjectiveSpace n //
    ∃ v : { v : Fin n → ℚ // v ≠ 0 },
      Quotient.mk (projectiveEquiv n) v = p ∧
      ∀ f ∈ eqs, MvPolynomial.eval v.val f = 0 }

structure IrreducibleCurveOverQ where
  n : ℕ
  definingEquations : Set (MvPolynomial (Fin n) ℚ)
  genus : ℕ
  isHomogeneous : ∀ f ∈ definingEquations, ∃ d : ℕ, f.IsHomogeneous d
  isIrreducible : (Ideal.span definingEquations).IsPrime
  isCurve : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ Ideal.span definingEquations) = 2
  genus_of_plane_curve : definingEquations.ncard = 1 → n = 3 →
    ∃ (d : ℕ) (f : MvPolynomial (Fin n) ℚ),
      f ∈ definingEquations ∧ f.IsHomogeneous d ∧ genus = (d - 1) * (d - 2) / 2

namespace IrreducibleCurveOverQ

def ratPoints (C : IrreducibleCurveOverQ) : Type :=
  projectiveRatPoints C.n C.definingEquations

end IrreducibleCurveOverQ

