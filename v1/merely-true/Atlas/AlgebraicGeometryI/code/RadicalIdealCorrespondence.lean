/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

open PrimeSpectrum Ideal

noncomputable section

section GaloisConnection

variable (R : Type*) [CommSemiring R]

/-- The fundamental Galois connection (Thm 1.2, Lec 1) between ideals of `R`
and closed subsets of `Spec R`, given by `zeroLocus ⊣ vanishingIdeal`. -/
theorem gc_zeroLocus_vanishingIdeal :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _
      (fun I => PrimeSpectrum.zeroLocus I) fun t => PrimeSpectrum.vanishingIdeal t :=
  PrimeSpectrum.gc R

/-- Abstract Nullstellensatz on `Spec R`: the vanishing ideal of the zero locus
of `I` is the radical of `I`. -/
theorem abstract_nullstellensatz (I : Ideal R) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set R)) = I.radical :=
  PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I

/-- For a radical ideal `I`, the vanishing ideal of its zero locus recovers `I`
itself — half of the radical-ideal correspondence (Thm 1.2). -/
theorem vanishingIdeal_zeroLocus_of_isRadical (I : Ideal R) (hI : I.IsRadical) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set R)) = I := by
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

/-- The zero locus of the vanishing ideal of `t` recovers the closure of `t`
in the Zariski topology of `Spec R`. -/
theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (PrimeSpectrum R)) :
    PrimeSpectrum.zeroLocus ↑(PrimeSpectrum.vanishingIdeal t) = closure t :=
  PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure t

/-- Two ideals have the same zero locus iff they share the same radical, the
order-theoretic injectivity statement of Thm 1.2. -/
theorem zeroLocus_eq_iff_radical_eq {I J : Ideal R} :
    PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus J ↔ I.radical = J.radical :=
  PrimeSpectrum.zeroLocus_eq_iff

/-- The vanishing ideal of any subset of `Spec R` is always a radical ideal. -/
theorem isRadical_vanishingIdeal (s : Set (PrimeSpectrum R)) :
    (PrimeSpectrum.vanishingIdeal s).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal s

/-- The order-embedding `closeds(Spec R) ↪ Ideal R` provided by the radical
ideal correspondence (Thm 1.2), packaged as an `OrderEmbedding`. -/
def closedsEmbedding :
    (TopologicalSpace.Closeds (PrimeSpectrum R))ᵒᵈ ↪o Ideal R :=
  PrimeSpectrum.closedsEmbedding R

end GaloisConnection

section ClassicalNullstellensatz

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*}

/-- The classical Galois connection between ideals of `k[X_σ]` and subsets of
`K^σ`, given by `zeroLocus ⊣ vanishingIdeal`. -/
theorem nullstellensatz_galois_connection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → K))ᵒᵈ _ _
      (MvPolynomial.zeroLocus K) (MvPolynomial.vanishingIdeal k) :=
  MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection

/-- Hilbert's Nullstellensatz: over an algebraically closed field `K` and a
finite-variable polynomial ring, `I(V(I)) = √I`. -/
theorem nullstellensatz [IsAlgClosed K] [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-- Specialization of the Nullstellensatz to prime ideals: `I(V(P)) = P` for
any prime ideal `P` (since prime implies radical). -/
theorem nullstellensatz_prime [IsAlgClosed K] [Finite σ]
    (P : Ideal (MvPolynomial σ k)) [hP : P.IsPrime] :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K P) = P :=
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P

/-- Weak Nullstellensatz: maximal ideals of `k[X_σ]` correspond to single
points in `K^σ` when `K/k` is algebraically closed. -/
theorem weak_nullstellensatz [IsAlgClosed K] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsMaximal) :
    ∃ x : σ → K, I = MvPolynomial.vanishingIdeal k {x} :=
  MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hI

end ClassicalNullstellensatz

section IrreducibilityAndPrimes

variable {R : Type*} [CommSemiring R]

/-- The zero locus of `I` is irreducible iff `√I` is a prime ideal —
the irreducible-closed-subset / prime-ideal correspondence. -/
theorem irreducible_zeroLocus_iff_prime (I : Ideal R) :
    IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  PrimeSpectrum.isIrreducible_zeroLocus_iff I

/-- For a radical ideal `I`, irreducibility of `V(I)` is equivalent to `I`
being prime. -/
theorem irreducible_zeroLocus_iff_prime_of_radical (I : Ideal R) (hI : I.IsRadical) :
    IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) ↔ I.IsPrime :=
  PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I hI

/-- A subset of `Spec R` is irreducible iff its vanishing ideal is prime. -/
theorem isIrreducible_iff_vanishingIdeal_isPrime {s : Set (PrimeSpectrum R)} :
    IsIrreducible s ↔ (PrimeSpectrum.vanishingIdeal s).IsPrime :=
  PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime

/-- The image of irreducible subsets of `Spec R` under the vanishing-ideal map
is exactly the set of prime ideals. -/
theorem vanishingIdeal_irreducible_eq_primes :
    PrimeSpectrum.vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
  PrimeSpectrum.vanishingIdeal_isIrreducible

/-- The vanishing-ideal map restricted to closed irreducible subsets gives a
bijection onto the prime ideals (a refinement of Thm 1.2 to irreducibles). -/
theorem vanishingIdeal_closed_irreducible_eq_primes :
    PrimeSpectrum.vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} =
      {P | P.IsPrime} :=
  PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible

/-- `Spec R` is irreducible iff the nilradical of `R` is prime — equivalent to
having a unique minimal prime. -/
theorem specIrreducible_iff_isPrime_nilradical :
    IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical

end IrreducibilityAndPrimes

section IrreducibleDomain

variable {R : Type*} [CommRing R]

/-- For a reduced ring, `Spec R` is irreducible iff `R` is an integral domain. -/
theorem specIrreducible_iff_isDomain [IsReduced R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ IsDomain R := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical, nilradical_eq_zero R]
  exact ⟨fun _ => IsDomain.of_bot_isPrime R, fun _ => Ideal.isPrime_bot⟩

/-- For an integral domain `R`, the prime spectrum `Spec R` is irreducible. -/
theorem specIrreducible_of_isDomain [IsDomain R] :
    IrreducibleSpace (PrimeSpectrum R) :=
  PrimeSpectrum.irreducibleSpace

end IrreducibleDomain

section RadicalDecomposition

variable {R : Type*} [CommSemiring R]

/-- The radical of `I` equals the infimum of all primes containing `I`. -/
theorem radical_eq_sInf_primes (I : Ideal R) :
    I.radical = sInf {J : Ideal R | I ≤ J ∧ J.IsPrime} :=
  Ideal.radical_eq_sInf I

/-- Sharper form: the radical equals the infimum of `I.minimalPrimes`. -/
theorem radical_eq_sInf_minimalPrimes (I : Ideal R) :
    I.radical = sInf I.minimalPrimes :=
  (Ideal.sInf_minimalPrimes).symm

/-- In a Noetherian ring, every ideal has only finitely many minimal primes. -/
theorem finite_minimalPrimes_of_noetherian [IsNoetherianRing R] (I : Ideal R) :
    I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing R I

/-- In a Noetherian ring, the radical of any ideal is a finite intersection
of prime ideals — the basis of primary decomposition. -/
theorem radical_eq_finite_iInf_primes [IsNoetherianRing R] (I : Ideal R) :
    ∃ (S : Finset (Ideal R)),
      (∀ J ∈ S, J.IsPrime) ∧ I.radical = S.inf id := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro J hJ
    rw [Set.Finite.mem_toFinset] at hJ
    exact hJ.1.1
  · rw [← Ideal.sInf_minimalPrimes]
    conv_lhs => rw [show I.minimalPrimes = ↑hfin.toFinset from (hfin.coe_toFinset).symm]
    exact (Finset.inf_id_eq_sInf hfin.toFinset).symm

/-- In a Noetherian ring, a radical ideal is itself a finite intersection of
primes, recovering its primary decomposition with no embedded components. -/
theorem isRadical_eq_finite_iInf_primes [IsNoetherianRing R] (I : Ideal R) (hI : I.IsRadical) :
    ∃ (S : Finset (Ideal R)),
      (∀ J ∈ S, J.IsPrime) ∧ I = S.inf id := by
  obtain ⟨S, hS, heq⟩ := radical_eq_finite_iInf_primes I
  exact ⟨S, hS, hI.radical ▸ heq⟩

/-- In a Noetherian ring, the set of global minimal primes is finite. -/
theorem finite_minimalPrimes_of_noetherian_ring [IsNoetherianRing R] :
    (minimalPrimes R).Finite :=
  minimalPrimes.finite_of_isNoetherianRing R

end RadicalDecomposition

end
