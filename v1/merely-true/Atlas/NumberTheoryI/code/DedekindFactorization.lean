/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors

section UniqueFactorizationFractionalIdeals

theorem FractionalIdeal.unique_factorization_exists
    {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I) = I :=
  FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

theorem FractionalIdeal.unique_factorization_unique
    {I : FractionalIdeal R⁰ K} (_hI : I ≠ 0)
    (e : HeightOneSpectrum R → ℤ)
    (he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0)
    (hprod : ∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ e v = I)
    (v : HeightOneSpectrum R) :
    e v = FractionalIdeal.count K v I := by
  have h1 : FractionalIdeal.count K v
    (∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ K) ^ e w) = e v :=
    FractionalIdeal.count_finprod K v e he
  rw [hprod] at h1
  exact h1.symm

theorem FractionalIdeal.unique_factorization {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I) = I) ∧
    (∀ (e : HeightOneSpectrum R → ℤ),
      (∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0) →
      (∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ e v = I) →
      ∀ v : HeightOneSpectrum R, e v = FractionalIdeal.count K v I) :=
  ⟨FractionalIdeal.unique_factorization_exists K hI,
   fun e he hprod v => FractionalIdeal.unique_factorization_unique K hI e he hprod v⟩

end UniqueFactorizationFractionalIdeals
