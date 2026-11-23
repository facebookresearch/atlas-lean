/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace
import Mathlib.Order.Minimal
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Order.KrullDimension

open TopologicalSpace Set

universe u

namespace NoetherianTopological

/-- The prime spectrum of a Noetherian ring is a Noetherian topological space: every
descending chain of closed subsets stabilises (Corollary 3, Lecture 2). -/
theorem primeSpectrum_noetherianSpace (R : Type u) [CommSemiring R] [IsNoetherianRing R] :
    NoetherianSpace (PrimeSpectrum R) :=
  inferInstance

/-- A Noetherian ring has only finitely many minimal primes; this is the algebraic
counterpart of the finite decomposition into irreducible components (Proposition 5). -/
theorem noetherian_finite_minimalPrimes (R : Type u) [CommSemiring R] [IsNoetherianRing R] :
    (minimalPrimes R).Finite :=
  minimalPrimes.finite_of_isNoetherianRing R

/-- The intersection of all minimal primes of a commutative semiring equals the
nilradical. -/
theorem sInf_minimalPrimes_eq_nilradical (R : Type*) [CommSemiring R] :
    sInf (minimalPrimes R) = nilradical R := by
  show sInf (Ideal.minimalPrimes ⊥) = nilradical R
  rw [Ideal.sInf_minimalPrimes]
  rfl

/-- For a reduced ring, the intersection of all minimal primes is the zero ideal. -/
theorem reduced_sInf_minimalPrimes (R : Type*) [CommSemiring R] [IsReduced R] :
    sInf (minimalPrimes R) = (⊥ : Ideal R) := by
  rw [sInf_minimalPrimes_eq_nilradical]
  exact nilradical_eq_zero R

/-- A preorder is catenary if any two saturated chains with the same endpoints have
the same length. -/
def IsCatenary (α : Type*) [Preorder α] : Prop :=
  ∀ (s₁ s₂ : LTSeries α),

    s₁.toFun 0 = s₂.toFun 0 →

    s₁.toFun (Fin.last s₁.length) = s₂.toFun (Fin.last s₂.length) →

    (∀ i : Fin s₁.length, s₁.toFun i.castSucc ⋖ s₁.toFun i.succ) →

    (∀ i : Fin s₂.length, s₂.toFun i.castSucc ⋖ s₂.toFun i.succ) →

    s₁.length = s₂.length

/-- A commutative ring is catenary if its prime spectrum is a catenary poset. -/
def IsRingCatenary (R : Type*) [CommRing R] : Prop :=
  IsCatenary (PrimeSpectrum R)


end NoetherianTopological
