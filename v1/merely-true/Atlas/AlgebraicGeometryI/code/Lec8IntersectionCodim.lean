/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

noncomputable section
open Ideal

/-- Krull dimension of a commutative ring as a natural number
(returning `0` in degenerate or infinite cases). -/
def dimNat (R : Type*) [CommRing R] : ℕ :=
  (Option.getD (ringKrullDim R) ⊤).toNat




/-- A minimal prime over `I + J` in a noetherian ring has height at
most the sum of the span-ranks of `I` and `J` (via Krull's height
theorem). -/
theorem height_minPrime_sup_le_spanRank_add
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (P : Ideal R)
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    P.height ≤ Cardinal.toENat (Submodule.spanRank I) +
               Cardinal.toENat (Submodule.spanRank J) :=
  calc P.height
      ≤ Cardinal.toENat (Submodule.spanRank (I ⊔ J)) :=
        Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hP
    _ ≤ Cardinal.toENat (Submodule.spanRank I + Submodule.spanRank J) :=
        OrderHomClass.mono Cardinal.toENat Submodule.spanRank_sup_le_sum_spanRank
    _ = Cardinal.toENat (Submodule.spanRank I) + Cardinal.toENat (Submodule.spanRank J) :=
        map_add Cardinal.toENat _ _

/-- A minimal prime over `I + J` in a noetherian ring has height at
most the sum of the (finite) span-ranks of `I` and `J`. -/
theorem height_minPrime_sup_le_spanFinrank_add
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (P : Ideal R)
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    P.height ≤ ↑(Submodule.spanFinrank I + Submodule.spanFinrank J) := by
  have h := height_minPrime_sup_le_spanRank_add I J P hP

  have hfgI : I.FG := IsNoetherian.noetherian I
  have hfgJ : J.FG := IsNoetherian.noetherian J
  have hltI := Submodule.spanRank_finite_iff_fg.mpr hfgI
  have hltJ := Submodule.spanRank_finite_iff_fg.mpr hfgJ
  obtain ⟨nI, hI⟩ := Cardinal.lt_aleph0.mp hltI
  obtain ⟨nJ, hJ⟩ := Cardinal.lt_aleph0.mp hltJ
  simp only [Submodule.spanFinrank, hI, hJ, Cardinal.toNat_natCast] at h ⊢
  simpa [Cardinal.toENat_nat] using h

end
