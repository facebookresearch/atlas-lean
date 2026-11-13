/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Divisors

namespace CurveDivisor

variable {C : Type*}

def IsEffective (D : CurveDivisor C) : Prop := ∀ P, 0 ≤ D P


theorem isEffective_iff_nonneg (D : CurveDivisor C) : D.IsEffective ↔ 0 ≤ D := by
  rw [IsEffective, Finsupp.le_def]
  simp

theorem le_iff_isEffective_sub (D₁ D₂ : CurveDivisor C) :
    D₁ ≤ D₂ ↔ (D₂ - D₁).IsEffective := by
  rw [isEffective_iff_nonneg, sub_nonneg]


theorem IsEffective.add {D₁ D₂ : CurveDivisor C}
    (h₁ : D₁.IsEffective) (h₂ : D₂.IsEffective) : (D₁ + D₂).IsEffective := by
  intro P
  simp only [Finsupp.coe_add, Pi.add_apply]
  linarith [h₁ P, h₂ P]


noncomputable def positivePart (D : CurveDivisor C) : CurveDivisor C :=
  Finsupp.mapRange (fun n => max n 0) (by simp) D

noncomputable def negativePart (D : CurveDivisor C) : CurveDivisor C :=
  Finsupp.mapRange (fun n => max (-n) 0) (by simp) D

@[simp]
theorem positivePart_apply (D : CurveDivisor C) (P : C) :
    D.positivePart P = max (D P) 0 := by
  simp [positivePart, Finsupp.mapRange_apply]

@[simp]
theorem negativePart_apply (D : CurveDivisor C) (P : C) :
    D.negativePart P = max (-(D P)) 0 := by
  simp [negativePart, Finsupp.mapRange_apply]

theorem positivePart_isEffective (D : CurveDivisor C) :
    D.positivePart.IsEffective := by
  intro P
  simp


theorem decomposition (D : CurveDivisor C) :
    D = D.positivePart - D.negativePart := by
  ext P
  simp only [positivePart_apply, negativePart_apply, Finsupp.coe_sub, Pi.sub_apply]
  omega


end CurveDivisor
