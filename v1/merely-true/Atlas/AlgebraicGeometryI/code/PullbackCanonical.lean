/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.unusedSectionVars false

open scoped nonZeroDivisors

namespace PullbackCanonical

section PullbackDef

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S]
variable [Algebra R S] [Module.IsTorsionFree R S]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]

/-- The pullback ring homomorphism on fractional ideals along `R → S`: extension of
scalars from fractional ideals in the fraction field `K` of `R` to fractional ideals
in the fraction field `L` of `S`. -/
noncomputable def pullbackDivisor :
    FractionalIdeal R⁰ K →+* FractionalIdeal S⁰ L :=
  FractionalIdeal.extendedHomₐ L S

/-- On the embedding of an ordinary ideal `I` of `R`, the pullback agrees with the
extension `I · S`. -/
theorem pullbackDivisor_coeIdeal (I : Ideal R) :
    pullbackDivisor R S K L (I : FractionalIdeal R⁰ K) =
      (I.map (algebraMap R S) : FractionalIdeal S⁰ L) :=
  FractionalIdeal.extendedHomₐ_coeIdeal_eq_map L S I

/-- The pullback respects multiplication of fractional ideals. -/
theorem pullbackDivisor_mul (I J : FractionalIdeal R⁰ K) :
    pullbackDivisor R S K L (I * J) =
      pullbackDivisor R S K L I * pullbackDivisor R S K L J :=
  map_mul (pullbackDivisor R S K L) I J

/-- The pullback sends the unit fractional ideal to the unit fractional ideal. -/
theorem pullbackDivisor_one :
    pullbackDivisor R S K L (1 : FractionalIdeal R⁰ K) = 1 :=
  map_one (pullbackDivisor R S K L)

end PullbackDef

section DegreeFormula

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S]
variable [IsIntegrallyClosed R] [IsIntegrallyClosed S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
variable [Module.Free ℤ R] [Module.Free ℤ S] [Module.Finite ℤ S] [Module.Finite ℤ R]

/-- The degree `[Frac S : Frac R]` of the field extension of fraction fields. -/
noncomputable def extensionDegree : ℕ := by
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  exact Module.finrank (FractionRing R) (FractionRing S)

/-- For a finite extension of Dedekind domains, the absolute norm of the pulled-back
ideal `I · S` equals `(N(I))^[Frac S : Frac R]`. -/
theorem absNorm_pullbackIdeal (I : Ideal R) :
    Ideal.absNorm (I.map (algebraMap R S)) =
      (Ideal.absNorm I) ^ extensionDegree R S := by
  unfold extensionDegree
  exact Ideal.absNorm_algebraMap R S I

/-- Degree-of-pullback formula for the canonical divisor: `deg(K_Y · S) = deg(K_Y) ·
[Frac S : Frac R]`, stated at the level of absolute norms. -/
theorem degPullback_canonical (K_Y : Ideal R) :
    Ideal.absNorm (K_Y.map (algebraMap R S)) =
      (Ideal.absNorm K_Y) ^ extensionDegree R S :=
  absNorm_pullbackIdeal R S K_Y

end DegreeFormula

end PullbackCanonical
