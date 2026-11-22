/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

namespace AlgebraicHartogs

/-- A height-one prime ideal in a commutative ring, bundled with the proofs that it is
prime and has height exactly one. -/
structure HeightOnePrime (A : Type*) [CommRing A] where
  asIdeal : Ideal A
  isPrime : asIdeal.IsPrime
  height_eq : asIdeal.height = 1

attribute [instance] HeightOnePrime.isPrime

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A height-one prime is non-zero (the zero ideal has height 0 in a domain). -/
lemma HeightOnePrime.ne_bot (p : HeightOnePrime A) : p.asIdeal ≠ ⊥ := by
  intro h
  have h0 : (⊥ : Ideal A).height = 0 := by
    rw [Ideal.height_eq_primeHeight (I := (⊥ : Ideal A)),
        Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]; rfl
  have habs := p.height_eq; rw [h] at habs; simp [h0] at habs

section Hauptidealsatz
variable [IsNoetherianRing A]

/-- Krull's Hauptidealsatz: any nonzero non-unit element of a Noetherian domain is
contained in some height-one prime ideal. -/
theorem exists_height_one_prime_containing (a : A) (ha_ne : a ≠ 0) (ha_nu : ¬IsUnit a) :
    ∃ p : HeightOnePrime A, a ∈ p.asIdeal := by
  have hne_top : Ideal.span ({a} : Set A) ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne_top
  haveI : m.IsPrime := hm.isPrime
  obtain ⟨q, hq_min, _⟩ := Ideal.exists_minimalPrimes_le (J := m) hle
  have hq_prime := Ideal.minimalPrimes_isPrime hq_min
  have ha_q : a ∈ q := hq_min.1.2 (Ideal.mem_span_singleton_self a)
  have hq_le : q.height ≤ 1 := by
    have : Submodule.IsPrincipal (Ideal.span ({a} : Set A)) := ⟨⟨a, by simp⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq_min
  have hq_ge : 1 ≤ q.height := by
    rw [ENat.one_le_iff_ne_zero, Ideal.height_eq_primeHeight]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact ha_ne (Ideal.mem_bot.mp ((Set.mem_singleton_iff.mp h0) ▸ ha_q))
  exact ⟨⟨q, hq_prime, le_antisymm hq_le hq_ge⟩, ha_q⟩

end Hauptidealsatz

section Localization
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- An element of the fraction field K lying in every prime localization of A comes from
A itself; this is the algebraic Hartogs principle over all primes. -/
theorem mem_of_mem_all_prime_localizations (x : K)
    (hx : ∀ v : PrimeSpectrum A, x ∈ Localization.subalgebra.ofField K
      v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) :=
  Algebra.mem_bot.mp ((PrimeSpectrum.iInf_localization_eq_bot A K) ▸ (Algebra.mem_iInf.mpr hx))

section Dedekind
variable [IsDedekindDomain A]

/-- In a Dedekind domain, every nonzero prime ideal has height exactly one. -/
theorem height_eq_one_of_prime_ne_bot (p : Ideal A) [hp : p.IsPrime] (hne : p ≠ ⊥) :
    p.height = 1 := by
  apply le_antisymm
  · obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨q, hq_min, hq_le⟩ := Ideal.exists_minimalPrimes_le (J := p)
      ((Ideal.span_le).mpr (Set.singleton_subset_iff.mpr ha_mem))
    have hq_ne : q ≠ ⊥ := by
      intro h; rw [h] at hq_min
      exact ha_ne (Ideal.mem_bot.mp (hq_min.1.2 (Ideal.mem_span_singleton_self a)))
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq_min
    have : q = p := (inferInstance : q.IsPrime).isMaximal hq_ne |>.eq_of_le hp.ne_top hq_le
    rw [← this]
    have : Submodule.IsPrincipal (Ideal.span ({a} : Set A)) := ⟨⟨a, by simp⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq_min
  · rw [ENat.one_le_iff_ne_zero, Ideal.height_eq_primeHeight]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact hne (Set.mem_singleton_iff.mp h0)

/-- Algebraic Hartogs theorem for Dedekind domains: a fraction-field element regular at
every height-one prime is globally regular. -/
theorem algebraicHartogs_dedekind (x : K)
    (hx : ∀ v : IsDedekindDomain.HeightOneSpectrum A, x ∈ Localization.subalgebra.ofField K
      v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) :=
  Algebra.mem_bot.mp ((IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot A K) ▸
    (Algebra.mem_iInf.mpr hx))

/-- Equivalence between Mathlib's `HeightOneSpectrum` and our `HeightOnePrime`
structure for a Dedekind domain. -/
def equivHeightOneSpectrumPrime :
    IsDedekindDomain.HeightOneSpectrum A ≃ HeightOnePrime A where
  toFun v := ⟨v.asIdeal, v.isPrime, height_eq_one_of_prime_ne_bot v.asIdeal v.ne_bot⟩
  invFun p := ⟨p.asIdeal, p.isPrime, p.ne_bot⟩
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl

end Dedekind
end Localization
end AlgebraicHartogs
