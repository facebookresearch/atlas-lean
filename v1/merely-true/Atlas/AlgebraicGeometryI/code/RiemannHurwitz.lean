/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Algebraic.Integral
import Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Atlas.AlgebraicGeometryI.code.FiniteMorphismDimension
import Atlas.AlgebraicGeometryI.code.RiemannRochGeneral

noncomputable section

open Ideal Module

section FundamentalIdentity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  (K L : Type*) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [Module.Finite R S]

/-- Fundamental identity in ramification theory: the sum over primes `P` of `S`
above a maximal ideal `p` of `R` of `e_P · f_P` equals the field extension
degree `[L : K]`. -/
theorem fundamental_identity_ramification
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
      p.ramificationIdx P * p.inertiaDeg P =
        finrank K L :=
  sum_ramification_inertia S K L hp0

/-- Fundamental identity in the local case (DVR extension): `e · f = [L : K]`. -/
theorem fundamental_identity_local [IsLocalRing S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    p.ramificationIdx (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg (IsLocalRing.maximalIdeal S) = finrank K L :=
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0

end FundamentalIdentity

section Unramified

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- Abbreviation for `Algebra.IsUnramifiedAt R P`, naming the property that an
algebra `R → S` is unramified at the prime `P` of `S` lying over `p`. -/
abbrev IsUnramifiedAt' (p : Ideal R) (P : Ideal S) [P.IsPrime] [P.LiesOver p] : Prop :=
  Algebra.IsUnramifiedAt R P

/-- `R → S` is unramified over `p` if it is unramified at every prime `P`
of `S` lying over `p`. -/
def IsUnramifiedOver (p : Ideal R) : Prop :=
  ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p], Algebra.IsUnramifiedAt R P

/-- Being unramified at `P` implies the ramification index `e_P = 1`. -/
theorem ramificationIdx_eq_one_of_isUnramifiedAt'
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [hlo : P.LiesOver p]
    [IsDomain S] [IsNoetherianRing S] [Algebra.EssFiniteType R S]
    (h : IsUnramifiedAt' p P) (hP : P ≠ ⊥) :
    p.ramificationIdx P = 1 := by
  have hpq : p = P.under R := hlo.over
  subst hpq
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := R) hP

/-- For Dedekind domains in good characteristic, being unramified at `P` is
equivalent to `e_P = 1`. -/
theorem isUnramifiedAt'_iff_ramificationIdx_eq_one
    {p : Ideal R} {P : Ideal S} [P.IsPrime] [hlo : P.LiesOver p]
    [IsDedekindDomain S] [Algebra.EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (hP : P ≠ ⊥) :
    IsUnramifiedAt' p P ↔ p.ramificationIdx P = 1 := by
  have hpq : p = P.under R := hlo.over
  subst hpq
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP

end Unramified

section Discriminant

open Algebra

/-- For a finite separable field extension `K ⊆ L`, the discriminant with
respect to any basis is non-zero. -/
theorem discriminant_ne_zero_of_separable
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (b : Basis ι K L) : discr K b ≠ 0 :=
  discr_not_zero_of_basis K b

/-- For a finite separable field extension, the discriminant is a unit. -/
theorem discriminant_isUnit_of_separable
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    (b : Basis ι K L) : IsUnit (discr K b) :=
  discr_isUnit_of_basis K b

end Discriminant

section RamificationBounds

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  (K L : Type*) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [Module.Finite R S]

/-- The number of primes above `p` is bounded by `[L : K]`. -/
theorem card_primes_over_le_finrank [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Finset.card (primesOverFinset p S) ≤ finrank K L :=
  card_primesOverFinset_le_finrank S K L hp0

/-- Sum of ramification indices over primes above `p` is bounded by `[L : K]`. -/
theorem sum_ramificationIdx_le_finrank [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
      p.ramificationIdx P ≤ finrank K L := by
  rw [← sum_ramification_inertia S K L hp0]
  apply Finset.sum_le_sum
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  exact Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)

/-- Each ramification index `e_P` is bounded by `[L : K]`. -/
theorem ramificationIdx_le_finrank' [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    p.ramificationIdx P ≤ finrank K L :=
  ramificationIdx_le_finrank S K L P

/-- Each inertia degree `f_P` is bounded by `[L : K]`. -/
theorem inertiaDeg_le_finrank' [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hp0 : p ≠ ⊥) :
    inertiaDeg p P ≤ finrank K L :=
  inertiaDeg_le_finrank S K L P hp0

end RamificationBounds

section Chevalley

/-- Lying-over for Dedekind domains: any non-zero prime `p` of `R` has a prime
`P` of `S` lying over it, when `R ⊆ S` is a finite faithfully flat extension. -/
theorem dedekind_lying_over
    (R S : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    (p : Ideal R) [hp : p.IsPrime] (_hp0 : p ≠ ⊥) :
    ∃ (P : Ideal S), P.IsPrime ∧ P.LiesOver p := by

  have hSurj := finite_morphism_spec_surjective R S
  obtain ⟨Q, hQ⟩ := hSurj ⟨p, hp⟩
  refine ⟨Q.asIdeal, Q.isPrime, ⟨?_⟩⟩
  have : PrimeSpectrum.comap (algebraMap R S) Q = ⟨p, hp⟩ := hQ
  simp [PrimeSpectrum.comap] at this
  exact this.symm

/-- The contraction of a prime ideal of `S` is a prime ideal of `R`. -/
theorem dedekind_contraction_is_prime
    (R S : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S]
    (P : Ideal S) [hP : P.IsPrime] :
    (P.comap (algebraMap R S)).IsPrime :=
  Ideal.IsPrime.comap (algebraMap R S)

/-- Every prime ideal `P` of `S` lies over its contraction `P ∩ R`. -/
instance dedekind_liesOver_contraction
    (R S : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S]
    (P : Ideal S) :
    P.LiesOver (P.under R) :=
  Ideal.over_under P

end Chevalley

section RamificationDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]

/-- The set of primes of `S` above a non-zero maximal ideal `p` of `R` is finite. -/
theorem primes_over_finite [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Set.Finite (primesOver p S) := by
  rw [← coe_primesOverFinset hp0 S]
  exact (primesOverFinset p S).finite_toSet

end RamificationDivisor

section RiemannHurwitzFormula

/-- Local contribution at `p` to the ramification divisor: the sum
`∑_{P|p} (e_P - 1)`. -/
def totalRamificationAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

/-- The local ramification at `p` is non-negative. -/
theorem totalRamificationAt_nonneg
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    0 ≤ totalRamificationAt S p hp0 := by
  unfold totalRamificationAt
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

/-- The local ramification at `p` is bounded by the field extension degree
`[L : K]`. -/
theorem totalRamificationAt_le_finrank
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    totalRamificationAt S p hp0 ≤ finrank K L := by
  unfold totalRamificationAt
  have hfund := sum_ramification_inertia S K L hp0
  calc ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P : ℤ) - 1)
    ≤ ∑ P ∈ primesOverFinset p S,
      (p.ramificationIdx P : ℤ) := by
        apply Finset.sum_le_sum; intro P _; omega
    _ ≤ ∑ P ∈ primesOverFinset p S,
        ((p.ramificationIdx P * p.inertiaDeg P : ℕ) : ℤ) := by
        apply Finset.sum_le_sum
        intro P hP
        have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
        have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
        exact_mod_cast Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)
    _ = (finrank K L : ℤ) := by exact_mod_cast hfund

/-- The local ramification at `p` vanishes iff every prime above `p` is
unramified. -/
theorem totalRamificationAt_eq_zero_iff
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    totalRamificationAt S p hp0 = 0 ↔
      ∀ P ∈ primesOverFinset p S,
        p.ramificationIdx P = 1 := by
  unfold totalRamificationAt
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h P hP
      have := h P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
      omega
    · intro h P hP
      simp [h P hP]
  · intro P hP
    have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
    have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    omega

/-- Numerical Riemann–Hurwitz: given pullback identity and canonical
decomposition, `2 g_X - 2 = n(2 g_Y - 2) + deg R`. -/
theorem riemann_hurwitz_formula
    (n g_X g_Y : ℤ) (deg_R deg_KX deg_KY deg_pullback : ℤ)
    (h_deg_KX : deg_KX = 2 * g_X - 2)
    (h_deg_KY : deg_KY = 2 * g_Y - 2)
    (h_pullback : deg_pullback = n * deg_KY)
    (h_canonical : deg_KX = deg_pullback + deg_R) :
    2 * g_X - 2 = n * (2 * g_Y - 2) + deg_R := by
  subst h_deg_KX; subst h_deg_KY; subst h_pullback; linarith

/-- Solving Riemann–Hurwitz for the ramification divisor degree. -/
theorem riemann_hurwitz_ramification_eq
    (n g_X g_Y R : ℤ)
    (hRH : 2 * g_X - 2 = n * (2 * g_Y - 2) + R) :
    R = 2 * g_X - 2 - n * (2 * g_Y - 2) := by linarith

/-- Riemann–Hurwitz genus bound: `g_X ≥ n g_Y - n + 1`. -/
theorem riemann_hurwitz_genus_bound
    (n g_X g_Y R : ℤ) (hR : 0 ≤ R)
    (hRH : 2 * g_X - 2 = n * (2 * g_Y - 2) + R) :
    g_X ≥ n * g_Y - n + 1 := by linarith

/-- Riemann–Hurwitz formulated using the algebraic `arithmeticGenus`. -/
theorem riemann_hurwitz_with_arithmeticGenus
    (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Algebra k A] [Module.Finite k A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra k B] [Module.Finite k B]
    (n : ℤ) (total_ramification : ℤ)
    (h_formula : (2 : ℤ) * RiemannRochGeneral.arithmeticGenus k B - 2 =
      n * (2 * RiemannRochGeneral.arithmeticGenus k A - 2) + total_ramification) :
    total_ramification =
      2 * (RiemannRochGeneral.arithmeticGenus k B : ℤ) - 2 -
        n * (2 * RiemannRochGeneral.arithmeticGenus k A - 2) := by
  linarith

/-- Numerical Riemann–Hurwitz identity for a hyperelliptic double cover of `ℙ¹`. -/
theorem riemann_hurwitz_hyperelliptic (g : ℤ) :
    2 * g - 2 = 2 * (2 * 0 - 2) + (2 * g + 2) := by ring

/-- The ramification divisor of a hyperelliptic curve of genus `g` over `ℙ¹`
has degree `2g + 2`. -/
theorem riemann_hurwitz_hyperelliptic_ramification (g R : ℤ)
    (hRH : 2 * g - 2 = 2 * (2 * 0 - 2) + R) :
    R = 2 * g + 2 := by linarith

end RiemannHurwitzFormula

end
