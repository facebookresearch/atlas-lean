/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open scoped nonZeroDivisors

namespace Hauptidealsatz

variable {R : Type*} [CommRing R] [IsDomain R]

/-- For a nonzero element `g` of a domain `R`, the Krull dimension drops by at most one
when passing to the quotient `R/(g)`. -/
theorem dim_quotient_ge_dim_minus_one (g : R) (hg : g ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {g}) + 1 ≤ ringKrullDim R :=
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg)

/-- Krull's Hauptidealsatz (Thm 5.4, Lec 5): In a Noetherian domain `R`, every minimal
prime over a nonzero non-unit principal ideal `(g)` has height exactly one. Geometrically,
each irreducible component of the zero locus `Z(g)` has codimension one. -/
theorem height_eq_one_of_mem_minimalPrimes_principal
    [IsNoetherianRing R]
    (g : R) (hg : g ≠ 0) (_hg_unit : ¬IsUnit g)
    (p : Ideal R) [p.IsPrime]
    (hp : p ∈ (Ideal.span {g}).minimalPrimes) :
    p.height = 1 := by

  have h_le : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp

  have h_ge : 1 ≤ p.height := by
    rw [Ideal.height_eq_primeHeight, ENat.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff] at h0

    have hgp : g ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton g))
    rw [h0] at hgp
    exact hg (Ideal.mem_bot.mp hgp)
  exact le_antisymm h_le h_ge

end Hauptidealsatz
