/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

noncomputable section

open PrimeSpectrum

namespace Proposition7

/-- The ramification locus of `A → B` (with `B` a free finite `A`-module) is
the zero locus of the discriminant; the closed set where the cover degenerates. -/
def ramificationLocus (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus {Algebra.discr A (Module.Free.chooseBasis A B)}

/-- Prop 7 (Lec 6): the ramification locus is closed in `Spec A`, being the
zero locus of a single discriminant element. -/
theorem ramificationLocus_isClosed (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] :
    IsClosed (ramificationLocus A B) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- If the discriminant is nonzero, the ramification locus is a proper closed
subset (not all of `Spec A`); this rules out total degeneration. -/
theorem ramificationLocus_ne_univ_of_discr_ne_zero
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B]
    (hd : Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0) :
    ramificationLocus A B ≠ Set.univ := by
  intro h
  have hmem := (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp h
  simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hmem
  rw [nilradical_eq_zero] at hmem
  exact hd hmem

/-- If the function-field extension `K → L` is separable and finite, the
discriminant of the integral extension `A → B` is nonzero. -/
theorem discr_ne_zero_of_separable_functionField
    (A : Type*) (K : Type*) (B : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [Algebra.IsSeparable K L] [Module.Finite K L] :
    Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0 := by
  set b := Module.Free.chooseBasis A B

  set b' := b.localizationLocalization K (nonZeroDivisors A) L

  have hlocal : Algebra.discr K b' = (algebraMap A K) (Algebra.discr A b) :=
    Algebra.discr_localizationLocalization A (nonZeroDivisors A) L b

  have hne : Algebra.discr K b' ≠ 0 := Algebra.discr_not_zero_of_basis K b'

  rw [hlocal] at hne


  exact fun h => hne (by rw [h, map_zero])

/-- Combined version of Prop 7: under a separable finite function-field
extension, the ramification locus is a proper closed subset of `Spec A`. -/
theorem ramificationLocus_ne_univ_of_separable
    (A : Type*) (K : Type*) (B : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [Algebra.IsSeparable K L] [Module.Finite K L] :
    ramificationLocus A B ≠ Set.univ :=
  ramificationLocus_ne_univ_of_discr_ne_zero A B
    (discr_ne_zero_of_separable_functionField A K B L)

end Proposition7
