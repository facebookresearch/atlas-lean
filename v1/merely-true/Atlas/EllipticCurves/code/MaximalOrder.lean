/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open NumberField

namespace MaximalOrder

/-- The ring of integers `𝓞 K` of a number field `K` is a `ℤ`-order: it is a free
`ℤ`-module whose rank equals the `ℚ`-dimension of `K`. This is the order property
needed for Theorem 12.26 (the ring of integers is the unique maximal order). -/
theorem ringOfIntegers_isOrder (K : Type*) [Field K] [NumberField K] :
    Module.Free ℤ (𝓞 K) ∧ Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
  ⟨inferInstance, RingOfIntegers.rank K⟩

/-- Any `ℤ`-order `O` in a number field `K` is contained in the integral closure
of `ℤ` in `K` (i.e. in `𝓞 K`). This is the "containment half" of Theorem 12.26
expressing that the ring of integers is the unique maximal order. -/
theorem ringOfIntegers_isMaximalOrder (K : Type*) [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] :
    O ≤ integralClosure ℤ K := by
  intro x hx
  exact (IsIntegral.of_finite ℤ (⟨x, hx⟩ : O)).algebraMap

/-- Theorem 12.26: the ring of integers `𝓞 K` of a number field `K` is the unique
maximal `ℤ`-order in `K`. If `O` is a `ℤ`-order that is maximal among finite
`ℤ`-orders containing it, then `O` equals the integral closure of `ℤ` in `K`. -/
theorem ringOfIntegers_unique_maximalOrder (K : Type*) [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O]
    (hmax : ∀ (O' : Subalgebra ℤ K), [Module.Finite ℤ O'] → O ≤ O' → O' ≤ O) :
    O = integralClosure ℤ K := by
  apply le_antisymm
  · exact ringOfIntegers_isMaximalOrder K O
  · haveI : Module.Finite ℤ ↥(integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact hmax (integralClosure ℤ K) (ringOfIntegers_isMaximalOrder K O)

end MaximalOrder
