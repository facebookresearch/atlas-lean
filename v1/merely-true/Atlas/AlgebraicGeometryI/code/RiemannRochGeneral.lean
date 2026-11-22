/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

open scoped TensorProduct
open nonZeroDivisors

noncomputable section

namespace RiemannRochGeneral

/-- Generic rank of an `A`-module `M` (for `A` a domain): the dimension over
`Frac A` of the base-change `Frac A ⊗_A M`. -/
def moduleRank (A : Type*) [CommRing A] [IsDomain A]
    (M : Type*) [AddCommGroup M] [Module A M] : ℕ :=
  Module.finrank (FractionRing A) (FractionRing A ⊗[A] M)

/-- Degree of a maximal ideal `I` of an algebra `A` over `k`: `dim_k (A / I)`. -/
def idealDegree (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] (I : Ideal A) [I.IsMaximal] : ℕ :=
  Module.finrank k (A ⧸ I)

/-- Degree of a line bundle ideal `J` of `A` over `k`: `dim_k (A / J)`. -/
def lineBundleDegree (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (J : Ideal A) : ℕ :=
  Module.finrank k (A ⧸ J)

/-- Arithmetic genus of a Dedekind algebra `A` over `k`: `dim_k Ω_{A/k}`. -/
def arithmeticGenus (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- The Kähler differentials of the polynomial ring `k[x]` are a free
`k[x]`-module of rank 1. -/
theorem kaehler_polynomial_rank (k : Type*) [Field k] :
    Module.finrank (Polynomial k) (Ω[Polynomial k⁄k]) = 1 := by
  rw [LinearEquiv.finrank_eq (KaehlerDifferential.polynomialEquiv k),
      Module.finrank_self]

/-- For a field `k`, the ideal `⊥` of `k` has degree 1 (since `k / ⊥ ≅ k`). -/
theorem idealDegree_bot_field (k : Type*) [Field k] :
    @idealDegree k _ k _ _ (Algebra.id k) ⊥ Ideal.bot_isMaximal = 1 := by
  unfold idealDegree
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k k).toLinearEquiv,
      Module.finrank_self]

/-- The unit ideal has line bundle degree zero. -/
theorem lineBundleDegree_top (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] : lineBundleDegree k A ⊤ = 0 := by
  unfold lineBundleDegree
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- For a maximal ideal `I`, the line bundle degree coincides with the
ideal degree. -/
theorem lineBundleDegree_eq_idealDegree (k : Type*) [Field k] (A : Type*)
    [CommRing A] [IsDomain A] [Algebra k A] (I : Ideal A) [I.IsMaximal] :
    lineBundleDegree k A I = idealDegree k A I := rfl

/-- Algebraic identity used in rank-one Riemann–Roch: `d + 1·(1 - g) = d + 1 - g`. -/
theorem riemann_roch_rank_one_identity (d : ℤ) (g : ℕ) :
    d + (1 : ℤ) * (1 - (g : ℤ)) = d + 1 - g := by ring

/-- The zero ideal has line bundle degree `dim_k A`. -/
theorem lineBundleDegree_bot (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] : lineBundleDegree k A ⊥ = Module.finrank k A := by
  unfold lineBundleDegree
  rw [LinearEquiv.finrank_eq (AlgEquiv.quotientBot k A).toLinearEquiv]

end RiemannRochGeneral
