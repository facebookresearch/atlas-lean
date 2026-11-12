/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.GoingUp

set_option maxHeartbeats 400000

/-- Lem 8, Lec 4: a finite morphism `A → B` sends a strict chain of primes
`p₁ ⊊ p₂` in `B` to a strict chain `p₁ ∩ A ⊊ p₂ ∩ A` in `A`. -/
theorem finite_map_strict_chains
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B]
    (p₁ p₂ : Ideal B) [p₁.IsPrime] [p₂.IsPrime]
    (h : p₁ < p₂) :
    p₁.comap (algebraMap A B) < p₂.comap (algebraMap A B) := by
  obtain ⟨h_le, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp h
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff h_le ⟨hx2, hx1⟩
    (Algebra.IsIntegral.isIntegral x)
