/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

noncomputable section

namespace WeilDivisor


/-- Group of Weil divisors on a "set of codim-1 subvarieties" `Y` (Def 29,
Lec 14): the free abelian group on `Y`, modelled as finitely supported
`ℤ`-valued functions. -/
abbrev Group (Y : Type*) := Y →₀ ℤ


/-- A Weil divisor is effective iff all of its coefficients are nonnegative. -/
def IsEffective {Y : Type*} (D : WeilDivisor.Group Y) : Prop :=
  ∀ y : Y, 0 ≤ D y


/-- The Weil divisor `n · [D]` consisting of `n` copies of a single
codim-1 subvariety `D`. -/
def single {Y : Type*} (D : Y) (n : ℤ) : WeilDivisor.Group Y :=
  Finsupp.single D n

/-- The coefficient of a Weil divisor `D` along a codim-1 subvariety `y`. -/
def coeff {Y : Type*} (D : WeilDivisor.Group Y) (y : Y) : ℤ :=
  D y


/-- Identification of the Weil divisor group with the abstract free abelian
group on `Y`. -/
def equivFreeAbelianGroup (Y : Type*) :
    WeilDivisor.Group Y ≃+ FreeAbelianGroup Y :=
  (FreeAbelianGroup.equivFinsupp Y).symm


/-- For a Dedekind domain, the Weil divisor group is the free abelian group on
the height-one primes. -/
abbrev DedekindGroup (R : Type*) [CommRing R] :=
  WeilDivisor.Group (IsDedekindDomain.HeightOneSpectrum R)


/-- The zero divisor is effective. -/
theorem isEffective_zero (Y : Type*) : IsEffective (0 : WeilDivisor.Group Y) := by
  intro y; simp

/-- A sum of effective divisors is effective. -/
theorem isEffective_add {Y : Type*} {D₁ D₂ : WeilDivisor.Group Y}
    (h₁ : IsEffective D₁) (h₂ : IsEffective D₂) : IsEffective (D₁ + D₂) := by
  intro y
  simp [Finsupp.add_apply]
  exact add_nonneg (h₁ y) (h₂ y)


end WeilDivisor

end
