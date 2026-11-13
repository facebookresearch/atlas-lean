/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization

open Ideal UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RiemannHurwitzSheaf

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- The different ideal `𝔡_{B/A}` is divisible by `P^{e_P - 1}` for each prime
`P` above a non-zero maximal ideal `p` of `A`. -/
theorem differentIdeal_dvd_pow_sub_one
    {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal] [P.LiesOver p]
    (hp : p ≠ ⊥) :
    P ^ (p.ramificationIdx P - 1) ∣ differentIdeal A B :=
  pow_sub_one_dvd_differentIdeal A P (p.ramificationIdx P) hp
    (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)




end RiemannHurwitzSheaf
