/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Ideal Module Finset

/-- The degree $[\kappa(\mathfrak{p}) : k]$ of a closed point $\mathfrak{p} \subseteq R$ over the base field $k$, defined as the dimension of the residue field $R/\mathfrak{p}$ as a $k$-vector space. -/
def closedPointDegree (k : Type*) [Field k] (R : Type*) [CommRing R] [Algebra k R]
    (p : Ideal R) : ℕ :=
  Module.finrank k (R ⧸ p)

/-- The degree of the pullback divisor of a prime $\mathfrak{p}$ under the inclusion $R \hookrightarrow S$: the weighted sum $\sum_{\mathfrak{P} \mid \mathfrak{p}} e(\mathfrak{P}/\mathfrak{p}) \cdot \deg(\mathfrak{P})$ over primes of $S$ lying above $\mathfrak{p}$. -/
def pullbackDivisorDegree (k : Type*) [Field k]
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra k R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra k S]
    (p : Ideal R) : ℕ :=
  (primesOverFinset p S).sum fun P =>
    p.ramificationIdx P * closedPointDegree k S P

/-- The degree of the pullback of a point under a finite morphism of Dedekind domains equals $[L:K] \cdot \deg(\mathfrak{p})$, where $K, L$ are the fraction fields: $\sum_{\mathfrak{P} \mid \mathfrak{p}} e(\mathfrak{P}/\mathfrak{p}) f(\mathfrak{P}/\mathfrak{p}) = [L:K]$. -/
theorem degree_pullback_eq_mul_degree
    (k : Type*) [Field k]
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra k R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra k S]
    [IsScalarTower k R S] [Module.IsTorsionFree R S]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    pullbackDivisorDegree k R S p = Module.finrank K L * closedPointDegree k R p := by
  unfold pullbackDivisorDegree closedPointDegree

  letI : Field (R ⧸ p) := Ideal.Quotient.field p


  have step1 : ∀ P ∈ primesOverFinset p S,
      p.ramificationIdx P * finrank k (S ⧸ P) =
      p.ramificationIdx P * p.inertiaDeg P * finrank k (R ⧸ p) := by
    intro P hP
    have hPprime : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have hPliesOver : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2

    have htower : finrank k (S ⧸ P) = finrank (R ⧸ p) (S ⧸ P) * finrank k (R ⧸ p) :=
      (finrank_mul_finrank k (R ⧸ p) (S ⧸ P)).symm ▸ (mul_comm _ _)

    rw [htower, Ideal.inertiaDeg_algebraMap, mul_assoc]
  rw [Finset.sum_congr rfl step1]


  rw [← Finset.sum_mul]

  rw [Ideal.sum_ramification_inertia S K L hp0]

end
