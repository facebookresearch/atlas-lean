/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.SpanRankOperations

noncomputable section

open scoped TensorProduct
open KaehlerDifferential Algebra IsLocalRing Module

universe u v

section Goal135

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The module `Ω[A⁄k]` of Kähler differentials of the `k`-algebra `A`. -/
def kaehlerDifferentialsModule : Type _ := Ω[A⁄k]

/-- The universal derivation `D : A → Ω[A⁄k]` satisfies the Leibniz rule
`D(ab) = a · D b + b · D a`. -/
theorem goal135_leibniz (a b : A) :
    KaehlerDifferential.D k A (a * b) =
      a • KaehlerDifferential.D k A b + b • KaehlerDifferential.D k A a :=
  (KaehlerDifferential.D k A).leibniz a b

/-- The universal derivation kills elements coming from the base ring `k`. -/
theorem goal135_map_algebraMap (r : k) :
    KaehlerDifferential.D k A (algebraMap k A r) = 0 :=
  (KaehlerDifferential.D k A).map_algebraMap r

/-- The image of the universal derivation spans `Ω[A⁄k]` as an `A`-module. -/
theorem goal135_span_range :
    Submodule.span A (Set.range (KaehlerDifferential.D k A)) = ⊤ :=
  KaehlerDifferential.span_range_derivation k A

end Goal135

section Goal136

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The universal property of `Ω[A⁄k]`: `A`-linear maps `Ω[A⁄k] → M` correspond naturally to
`k`-derivations `A → M`. -/
def goal136_universalProperty
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] :
    (Ω[A⁄k] →ₗ[A] M) ≃ₗ[A] Derivation k A M :=
  KaehlerDifferential.linearMapEquivDerivation k A

/-- The lift of a `k`-derivation `D'` through the universal derivation recovers `D'`. -/
theorem goal136_lift_comp
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (D' : Derivation k A M) :
    D'.liftKaehlerDifferential.compDer (KaehlerDifferential.D k A) = D' :=
  Derivation.liftKaehlerDifferential_comp D'

/-- Uniqueness in the universal property: two `A`-linear maps `Ω[A⁄k] → M` that compose to
the same derivation with `D` must be equal. -/
theorem goal136_lift_unique
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (f g : Ω[A⁄k] →ₗ[A] M)
    (hfg : f.compDer (KaehlerDifferential.D k A) = g.compDer (KaehlerDifferential.D k A)) :
    f = g :=
  Derivation.liftKaehlerDifferential_unique f g hfg

end Goal136

end
