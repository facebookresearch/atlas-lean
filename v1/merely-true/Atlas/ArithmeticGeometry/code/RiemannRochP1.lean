/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch
import Mathlib.FieldTheory.RatFunc.Basic

open RiemannRochSpace CurveDivisor CurveWithOrd

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]







/-- A nonzero rational function $f$ has prescribed poles given by an effective divisor $A$ if $\mathrm{div}(f) + A \geq 0$ and $\mathrm{ord}_P(f) = -A(P)$ for every $P$ with $A(P) > 0$. -/
def HasPrescribedPoles (f : Fˣ) (A : CurveDivisor C) : Prop :=
  (principalDivisor (C := C) f + A).IsEffective ∧
  ∀ P : C, A P > 0 → CurveWithOrd.ord (F := F) P f = -(A P)



/-- A function with prescribed poles bounded by $A$ lies in the Riemann-Roch space $L(A)$. -/
theorem mem_riemannRochSpace_of_prescribed_poles
    {f : Fˣ} {A : CurveDivisor C}
    (hf : HasPrescribedPoles (C := C) (F := F) (k := k) f A) :
    (f : F) ∈ riemannRochSpace (F := F) (k := k) A := by
  rw [mem_riemannRochSpace_iff]
  right
  refine ⟨Units.ne_zero f, ?_⟩
  have : Units.mk0 (↑f) (Units.ne_zero f) = f := Units.mk0_val f _
  rw [this]
  exact hf.1

/-- If $A \leq B$ as divisors then $\deg B - \deg A \geq 0$. -/
theorem degree_sub_nonneg_of_le
    {C : Type*} {A B : CurveDivisor C} (hAB : A ≤ B) :
    0 ≤ degree C B - degree C A := by
  have hBA_eff := (CurveDivisor.le_iff_isEffective_sub A B).mp hAB
  have h0 : 0 ≤ degree C (B - A) := by
    rw [CurveDivisor.degree_eq_sum]
    exact Finsupp.sum_nonneg (fun i _ => hBA_eff i)
  linarith [degree_sub B A]







end RiemannRochSpace
