/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.MinpolyDegreeBound
import Atlas.AlgebraicGeometryI.code.CardRootsLeDeg
import Atlas.AlgebraicGeometryI.code.FiberDegreeBound

noncomputable section

open Module Ideal Polynomial FiberDegreeBound
open scoped Classical

/-- Key chain inequality for Lec 6, Lem 13: the number of `K`-conjugates of an
element `α` in a finite extension `L/K` is at most `[L : K]`. -/
theorem lec6_lemma13_chain {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (α : L) :
    (minpoly K α).roots.toFinset.card ≤ finrank K L :=
  (card_roots_le_deg (minpoly K α)).trans (minpoly_natDegree_le_finrank α)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra


/-- Dedekind-domain instance of Lec 6, Lem 13: the number of primes of `S` lying
over a non-zero maximal `p ⊆ R` is bounded by `[L : K]`. -/
theorem lec6_lemma13_dedekind
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [NoZeroSMulDivisors R S]
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (primesOverFinset p S).card ≤ finrank K L :=
  fdb_fiber_card_le_degree K L hp0

/-- For a finite extension of domains, the field-of-fractions degree agrees with
the rank as a module: `[K(A):K(B)] = rank_B A`. -/
theorem lec6_degree_eq_finrank
    (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [FaithfulSMul B A] [Module.Finite B A] :
    degree B A = finrank B A :=
  degree_eq_finrank B A
