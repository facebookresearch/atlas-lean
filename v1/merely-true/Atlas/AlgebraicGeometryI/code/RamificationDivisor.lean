/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 800000

open IsDedekindDomain

/-- Algebraic data for a morphism of smooth curves: a pair of Dedekind domains
`R → S` corresponding to the coordinate rings of the source and target curves. -/
structure CurveMorphismData where
  R : Type*
  S : Type*
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [isDedekindR : IsDedekindDomain R]
  [isDedekindS : IsDedekindDomain S]
  [algebraRS : Algebra R S]

attribute [instance] CurveMorphismData.commRingR CurveMorphismData.commRingS
  CurveMorphismData.isDedekindR CurveMorphismData.isDedekindS
  CurveMorphismData.algebraRS

namespace CurveMorphismData

variable (φ : CurveMorphismData)

/-- The local ramification index `e_P = d_P` at a height-one prime `P` of the
target ring, the multiplicity with which `f^*(f(P))` contains `P`. -/
noncomputable def ramificationIndex (P : HeightOneSpectrum φ.S) : ℕ :=
  Ideal.ramificationIdx (P.asIdeal.comap (algebraMap φ.R φ.S)) P.asIdeal

/-- Coefficient `d_P − 1` of the ramification divisor at the prime `P`. -/
noncomputable def ramificationDivisorCoeff (P : HeightOneSpectrum φ.S) : ℤ :=
  (φ.ramificationIndex P : ℤ) - 1

/-- The ramification divisor `R = Σ (d_x − 1) x` as a function on the
height-one spectrum of the target curve (Lec 21). -/
noncomputable def ramificationDivisor : HeightOneSpectrum φ.S → ℤ :=
  φ.ramificationDivisorCoeff

/-- Degree of the ramification divisor over a finite set of primes,
i.e. `deg R = Σ_P (d_P − 1)`. -/
noncomputable def ramificationDivisorDegree (s : Finset (HeightOneSpectrum φ.S)) : ℤ :=
  ∑ P ∈ s, φ.ramificationDivisorCoeff P

/-- Predicate `P` is a ramification point: ramification index strictly greater than 1. -/
def IsRamifiedAt (P : HeightOneSpectrum φ.S) : Prop :=
  φ.ramificationIndex P > 1

end CurveMorphismData
