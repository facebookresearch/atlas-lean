/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic

noncomputable section

/-- Definition 35 (Lecture 18). The module of Kähler differentials `Ω[A⁄B]` of a `B`-algebra
`A`, providing the algebraic analogue of the cotangent bundle. -/
def Definition35_KahlerDifferentials
    (B : Type*) (A : Type*) [CommRing B] [CommRing A] [Algebra B A] :=
  Ω[A⁄B]

/-- The canonical universal `B`-linear derivation `d : A → Ω[A⁄B]` from Definition 35. -/
def Definition35_universalDerivation
    (B : Type*) (A : Type*) [CommRing B] [CommRing A] [Algebra B A] :
    Derivation B A Ω[A⁄B] :=
  KaehlerDifferential.D B A

/-- Universal property of Kähler differentials (Definition 35): `A`-linear maps
`Ω[A⁄B] → M` are in natural bijection with `B`-derivations `A → M`. -/
def Definition35_universalProperty
    (B : Type*) (A : Type*) [CommRing B] [CommRing A] [Algebra B A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M] :
    (Ω[A⁄B] →ₗ[A] M) ≃ₗ[A] Derivation B A M :=
  KaehlerDifferential.linearMapEquivDerivation B A

end
