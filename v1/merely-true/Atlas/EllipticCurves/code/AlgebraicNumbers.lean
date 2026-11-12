/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.NumberTheory.NumberField.Basic

namespace AlgebraicNumber

/-- A complex number is an algebraic number if it is algebraic over the rationals `ℚ`. -/
abbrev IsAlgebraicNumber (α : ℂ) : Prop := IsAlgebraic ℚ α

/-- A complex number is an algebraic integer if it is integral over `ℤ`, i.e. it is the
root of a monic polynomial with integer coefficients. -/
abbrev IsAlgebraicInteger (α : ℂ) : Prop := IsIntegral ℤ α

/-- Unfolds the definition of `IsAlgebraicNumber` as algebraicity over `ℚ`. -/
@[simp]
theorem isAlgebraicNumber_iff (α : ℂ) : IsAlgebraicNumber α ↔ IsAlgebraic ℚ α :=
  Iff.rfl

/-- Unfolds the definition of `IsAlgebraicInteger` as integrality over `ℤ`. -/
@[simp]
theorem isAlgebraicInteger_iff (α : ℂ) : IsAlgebraicInteger α ↔ IsIntegral ℤ α :=
  Iff.rfl

open NumberField

/-- Any finite `ℤ`-subalgebra `O` of a number field `K` is contained in the integral
closure of `ℤ` in `K`, i.e. in the ring of integers `𝓞 K`. This expresses that the
ring of integers is the maximal order in `K`. -/
theorem ringOfIntegers_isMaximalOrder (K : Type*) [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] :
    O ≤ integralClosure ℤ K := by
  intro x hx
  exact (IsIntegral.of_finite ℤ (⟨x, hx⟩ : O)).algebraMap

/-- The ring of integers `𝓞 K` of a number field `K` is unique up to ring isomorphism:
any other integral closure `R` of `ℤ` in `K` is canonically isomorphic to `𝓞 K`. -/
noncomputable def ringOfIntegers_unique (K : Type*) [Field K] [NumberField K]
    (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 K ≃+* R :=
  NumberField.RingOfIntegers.equiv R

end AlgebraicNumber
