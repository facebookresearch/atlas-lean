/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Data.Finset.Basic

open TopologicalSpace PrimeSpectrum Set

/-- Lecture 4, Proposition 5: a Noetherian topological space has finitely many irreducible
components, whose union is the whole space. -/
theorem noetherian_finite_union_irreducible_components
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    (irreducibleComponents X).Finite ∧ ⋃₀ irreducibleComponents X = univ :=
  ⟨NoetherianSpace.finite_irreducibleComponents, sUnion_irreducibleComponents⟩

/-- Existential form of Proposition 5: a Noetherian topological space admits some finite
covering by closed irreducible subsets. -/
theorem noetherian_finite_union_closed_irreducible
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧
      (∀ t ∈ S, IsIrreducible t) ∧ ⋃₀ S = univ := by
  obtain ⟨S, hf, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (isClosed_univ (X := X))
  exact ⟨S, hf, hc, hi, hU.symm ▸ rfl⟩

/-- The vanishing ideal of a finite union of subsets of `Spec R` is the infimum of the individual
vanishing ideals. -/
lemma vanishingIdeal_sUnion_finset {R : Type*} [CommRing R]
    (T : Finset (Set (PrimeSpectrum R))) :
    vanishingIdeal (⋃₀ ↑T) = T.inf (vanishingIdeal ·) := by
  induction T using Finset.cons_induction with
  | empty => simp [vanishingIdeal_empty]
  | cons a S haS ih =>
    rw [Finset.coe_cons, sUnion_insert, vanishingIdeal_union, Finset.inf_cons, ih]

/-- Ring-theoretic consequence of Proposition 5: in a Noetherian ring, every radical ideal is a
finite intersection of primes. -/
theorem radical_ideal_eq_finite_iInf_primes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.IsRadical) :
    ∃ (S : Finset (Ideal R)), (∀ P ∈ S, Ideal.IsPrime P) ∧ I = S.inf id := by

  obtain ⟨T, hTfin, _, hTirred, hTeq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_zeroLocus (↑I : Set R))
  lift T to Finset (Set (PrimeSpectrum R)) using hTfin
  refine ⟨T.image vanishingIdeal, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
    exact isIrreducible_iff_vanishingIdeal_isPrime.mp (hTirred t (Finset.mem_coe.mpr ht))
  ·
    have hI_eq : I = vanishingIdeal (zeroLocus (↑I : Set R)) := by
      rw [vanishingIdeal_zeroLocus_eq_radical]; exact hI.radical.symm
    rw [hI_eq, hTeq, vanishingIdeal_sUnion_finset, Finset.inf_image]
    simp

/-- A closed subset of `Spec R` is irreducible iff its vanishing ideal is prime. -/
theorem closed_irreducible_iff_vanishingIdeal_prime
    {R : Type*} [CommRing R] {Z : Set (PrimeSpectrum R)} (_hZ : IsClosed Z) :
    IsIrreducible Z ↔ (vanishingIdeal Z).IsPrime :=
  isIrreducible_iff_vanishingIdeal_isPrime
