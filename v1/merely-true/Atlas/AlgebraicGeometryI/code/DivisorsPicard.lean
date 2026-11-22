/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Ideal

noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard


/-- The Weil divisor group `DW(Y)` on `Y` (Def 29, Lec 14): finitely supported `ℤ`-valued
formal sums on `Y`, viewed as the free abelian group on points of `Y`. -/
abbrev WeilDivisorGroup (Y : Type*) := Y →₀ ℤ

/-- A Weil divisor is effective when all coefficients are non-negative. -/
def WeilDivisor.IsEffective {Y : Type*} (D : WeilDivisorGroup Y) : Prop :=
  ∀ y : Y, 0 ≤ D y


/-- An ideal class in the class group is trivial iff the ideal is principal: a concrete
realization of `Pic = DC / principals` (Cor 19, Lec 15) for Dedekind domains. -/
theorem pic_eq_divC_mod_principal (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] {I : Ideal A} (hI : I ∈ (Ideal A)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
  ClassGroup.mk0_eq_one_iff hI


/-- Two Cartier divisors (i.e. non-zero ideals) are linearly equivalent when they
represent the same class in the Picard group. -/
def CartierDivisor.LinearlyEquivalent (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (I J : (Ideal A)⁰) : Prop :=
  ClassGroup.mk0 I = ClassGroup.mk0 J


/-- A UFD that is also a Dedekind domain is a PID. -/
theorem ufd_dedekind_is_pid (R : Type*) [CommRing R]
    [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R

/-- For a Dedekind domain that is also a UFD, the ideal class group is trivial,
i.e. Pic is trivial: every ideal is principal. -/
theorem classGroup_subsingleton_of_ufd_dedekind (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (ClassGroup R) := by
  haveI : IsPrincipalIdealRing R := ufd_dedekind_is_pid R
  rw [← Fintype.card_le_one_iff_subsingleton]
  exact Nat.le_of_eq card_classGroup_eq_one

/-- In a UFD, every non-zero prime ideal contains a prime element. -/
theorem ufd_prime_contains_prime (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (P : Ideal R) [hP : P.IsPrime] (hne : P ≠ ⊥) :
    ∃ p ∈ P, Prime p :=
  hP.exists_mem_prime_of_ne_bot hne


/-- The Cartier-to-Weil divisor map: send a fractional ideal to its valuation
data, recording for each height-one prime the order of vanishing. -/
def cartierToWeilDivisor (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) :
    WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R) :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v I) (by
    have h := FractionalIdeal.finite_factors I
    rw [Filter.eventually_cofinite] at h
    exact h.subset fun v hv => hv)

/-- Reconstruct a non-zero fractional ideal from its Weil divisor data via the
finite product over height-one primes raised to the orders of vanishing. -/
theorem weilCartierFactorization (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^
        (cartierToWeilDivisor R K I v) = I := by
  have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI
  simp only [cartierToWeilDivisor, Finsupp.ofSupportFinite_coe] at key ⊢
  exact key

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
         (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] in
/-- Restriction of the Cartier-to-Weil map to invertible fractional ideals. -/
def cartierToWeilFun (I : (FractionalIdeal R⁰ K)ˣ) :
    WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R) :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v I.val) (by
    have h := FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)
    rw [Filter.eventually_cofinite] at h
    exact h.subset fun v hv => hv)

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
         (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] in
/-- The Weil-to-Cartier map: build an invertible fractional ideal as the product
of prime ideals raised to the orders specified by the Weil divisor. -/
def weilToCartierFun (D : WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R)) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (D.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n)) (by
    rw [Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- The multiplicative isomorphism between invertible fractional ideals (the
Cartier divisor group) and the free abelian group on height-one primes (the
Weil divisor group), proving `DC ≃ DW` for a Dedekind domain. -/
def cartierWeilIso (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ ≃*
      Multiplicative (WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R)) where
  toFun I := Multiplicative.ofAdd (cartierToWeilFun R K I)
  invFun D := weilToCartierFun R K (Multiplicative.toAdd D)
  left_inv I := by
    show weilToCartierFun R K (cartierToWeilFun R K I) = I
    ext1
    simp only [weilToCartierFun, Units.val_mk0]
    have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) (Units.ne_zero I)
    rw [Finsupp.prod]; symm; rw [← key]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, cartierToWeilFun,
      Finsupp.ofSupportFinite_coe, ne_eq]
    intro h; exact hv (by rw [h, zpow_zero])
  right_inv D := by
    show Multiplicative.ofAdd
      (cartierToWeilFun R K (weilToCartierFun R K (Multiplicative.toAdd D))) = D
    apply Multiplicative.ext
    show cartierToWeilFun R K (weilToCartierFun R K (Multiplicative.toAdd D)) =
      Multiplicative.toAdd D
    ext v
    simp only [cartierToWeilFun, Finsupp.ofSupportFinite_coe, weilToCartierFun, Units.val_mk0]
    exact FractionalIdeal.count_finsuppProd K v (Multiplicative.toAdd D)
  map_mul' I J := by
    show Multiplicative.ofAdd (cartierToWeilFun R K (I * J)) =
      Multiplicative.ofAdd (cartierToWeilFun R K I) *
        Multiplicative.ofAdd (cartierToWeilFun R K J)
    rw [← ofAdd_add]; apply Multiplicative.ext
    show cartierToWeilFun R K (I * J) =
      cartierToWeilFun R K I + cartierToWeilFun R K J
    ext v
    simp only [cartierToWeilFun, Units.val_mul, Finsupp.ofSupportFinite_coe,
      Finsupp.coe_add, Pi.add_apply,
      FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)]

/-- `Pic(R) = DC(R) / principals`: the class group is isomorphic to the
quotient of invertible fractional ideals by principal fractional ideals
(Cor 19, Lec 15). -/
def picIsomCartierQuotPrincipal (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ClassGroup R ≃* (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range :=
  ClassGroup.equiv K


/-- A ring is locally factorial when each localization at a prime ideal is a UFD;
the hypothesis under which Weil and Cartier divisors agree. -/
def IsLocallyFactorial (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime P)


/-- A discrete valuation ring is a UFD. -/
theorem dvr_is_ufd (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : UniqueFactorizationMonoid R :=
  inferInstance

/-- A discrete valuation ring is a PID. -/
theorem dvr_is_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : IsPrincipalIdealRing R :=
  inferInstance

/-- Every Dedekind domain is locally factorial: localizations at primes are DVRs
(non-zero primes) or fields (the zero prime), both of which are UFDs. -/
theorem dedekind_isLocallyFactorial (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] : IsLocallyFactorial R := by
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    haveI : Ideal.IsPrime (⊥ : Ideal R) := hP
    exact inferInstance
  · haveI := hP
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hbot _
    exact inferInstance

/-- Localizing a Dedekind domain at a non-zero prime gives a DVR. -/
instance dedekind_localization_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _

/-- Localizing a Dedekind domain at a non-zero prime gives a PID. -/
instance dedekind_localization_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    IsPrincipalIdealRing (Localization.AtPrime P) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    dedekind_localization_dvr R P hP
  exact inferInstance

/-- In a UFD, every minimal non-zero prime (i.e. height-one prime) is principal,
generated by a prime element. -/
theorem ufd_height_one_prime_isPrincipal (R : Type*) [CommRing R]
    [UniqueFactorizationMonoid R]
    (P : Ideal R) [hP : P.IsPrime] (hne : P ≠ ⊥)
    (hmin : ∀ (Q : Ideal R) [Q.IsPrime], Q ≤ P → Q ≠ ⊥ → Q = P) :
    Submodule.IsPrincipal P := by
  obtain ⟨p, hpP, hp⟩ := hP.exists_mem_prime_of_ne_bot hne
  have hp0 : p ≠ 0 := hp.ne_zero
  have hspan_prime : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
  have hspan_le : Ideal.span {p} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpP)
  have hspan_ne : Ideal.span {p} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [← @hmin (Ideal.span {p}) hspan_prime hspan_le hspan_ne]
  exact ⟨⟨p, rfl⟩⟩

/-- Under local factoriality, a height-one prime ideal becomes principal after
localizing at any prime: this is the local condition relating Weil and Cartier
divisors. -/
theorem ideal_locally_principal_of_locally_factorial (R : Type*) [CommRing R] [IsDomain R]
    (hlf : IsLocallyFactorial R)
    (I : Ideal R) [hI : I.IsPrime] (hIne : I ≠ ⊥)
    (hht1 : ∀ (Q : Ideal R) [Q.IsPrime], Q ≤ I → Q ≠ ⊥ → Q = I)
    (P : Ideal R) [hPprime : P.IsPrime] :
    Submodule.IsPrincipal (I.map (algebraMap R (Localization.AtPrime P))) := by
  by_cases hle : I ≤ P
  ·
    haveI hUFD : UniqueFactorizationMonoid (Localization.AtPrime P) := hlf P
    have hdisj : Disjoint (P.primeCompl : Set R) (I : Set R) := by
      rw [Set.disjoint_left]; intro x hx hxI; exact hx (hle hxI)
    have hImap_prime : (I.map (algebraMap R (Localization.AtPrime P))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ I hI hdisj
    have hImap_ne : I.map (algebraMap R (Localization.AtPrime P)) ≠ ⊥ := by
      intro h
      have : I = ⊥ := by
        rw [eq_bot_iff]; intro x hx
        have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) hx
        rw [h] at hmap; simp only [Ideal.mem_bot] at hmap
        exact (IsLocalization.injective (Localization.AtPrime P)
          P.primeCompl_le_nonZeroDivisors) (by rw [hmap, map_zero])
      exact hIne this

    have hImap_min : ∀ (J : Ideal (Localization.AtPrime P)) [J.IsPrime],
        J ≤ I.map (algebraMap R (Localization.AtPrime P)) → J ≠ ⊥ →
        J = I.map (algebraMap R (Localization.AtPrime P)) := by
      intro J hJprime hJle hJne
      have hJcomap_prime : (J.comap (algebraMap R (Localization.AtPrime P))).IsPrime :=
        Ideal.IsPrime.comap (algebraMap R (Localization.AtPrime P))
      have hJcomap_le : J.comap (algebraMap R (Localization.AtPrime P)) ≤ I := by
        calc J.comap (algebraMap R (Localization.AtPrime P))
            ≤ (I.map (algebraMap R (Localization.AtPrime P))).comap
                (algebraMap R (Localization.AtPrime P)) := Ideal.comap_mono hJle
          _ = I := IsLocalization.comap_map_of_isPrime_disjoint P.primeCompl _ hI hdisj
      have hJcomap_ne : J.comap (algebraMap R (Localization.AtPrime P)) ≠ ⊥ := by
        intro h; apply hJne
        have : J = (J.comap (algebraMap R (Localization.AtPrime P))).map
            (algebraMap R (Localization.AtPrime P)) :=
          (IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) J).symm
        rw [this, h, Ideal.map_bot]
      have heq := @hht1 _ hJcomap_prime hJcomap_le hJcomap_ne
      calc J = (J.comap (algebraMap R (Localization.AtPrime P))).map
            (algebraMap R (Localization.AtPrime P)) :=
          (IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) J).symm
        _ = I.map (algebraMap R (Localization.AtPrime P)) := by rw [heq]
    exact @ufd_height_one_prime_isPrincipal _ _ hUFD _ hImap_prime hImap_ne hImap_min
  ·
    have : I.map (algebraMap R (Localization.AtPrime P)) = ⊤ :=
      IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hle
    rw [this]
    exact ⟨⟨1, by simp⟩⟩

/-- Any ideal in a Dedekind domain becomes principal after localizing at a
non-zero prime, since the localization is a DVR (hence PID). -/
theorem ideal_locally_principal_dedekind (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (I : Ideal R)
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    Submodule.IsPrincipal (I.map (algebraMap R (Localization.AtPrime P))) := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    dedekind_localization_dvr R P hP
  haveI : IsPrincipalIdealRing (Localization.AtPrime P) := inferInstance
  exact IsPrincipalIdealRing.principal _

/-- The class group measures the obstruction between Weil and Cartier divisors:
a non-zero ideal represents the trivial class iff it is already principal. -/
theorem classGroup_measures_weil_cartier_obstruction (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ∈ (Ideal R)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
  ClassGroup.mk0_eq_one_iff hI


/-- The Picard group of the affine line `A¹_k = Spec k[x]` is trivial, since
`k[x]` is a PID. -/
theorem pic_affine_line_trivial (k : Type*) [Field k] :
    Fintype.card (ClassGroup (Polynomial k)) = 1 :=
  card_classGroup_eq_one


/-- Polynomial rings in arbitrarily many variables over a field are UFDs. -/
instance mvPolynomial_ufd (k : Type*) [Field k] (σ : Type*) :
    UniqueFactorizationMonoid (MvPolynomial σ k) :=
  MvPolynomial.uniqueFactorizationMonoid σ


/-- The power series ring over a PID is a UFD. -/
theorem power_series_ufd_of_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : UniqueFactorizationMonoid (PowerSeries R) :=
  inferInstance


/-- The class number of a PID is one: every PID has trivial Picard group. -/
theorem classNumber_one_of_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : Fintype.card (ClassGroup R) = 1 :=
  card_classGroup_eq_one

/-- For a Dedekind domain, the class group is trivial iff the ring is a PID. -/
theorem classGroup_trivial_iff_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Fintype (ClassGroup R)] :
    Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdealRing R :=
  card_classGroup_eq_one_iff


/-- Finitely generated torsion-free modules over a PID are free: a key step in
classifying coherent sheaves on `A¹` and in proving Grothendieck-Birkhoff. -/
theorem fg_torsionfree_free_of_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M] :
    Module.Free R M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  exact Module.Free.of_basis (Module.basisOfFiniteTypeTorsionFree hs).2


/-- The Cartier divisor group `DC(A)` (Def 30, Lec 15), realized as the units of
the monoid of fractional ideals. -/
abbrev CartierDivisorGroupUnits (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] := (FractionalIdeal A⁰ K)ˣ

/-- Alternative spelling of `CartierDivisorGroupUnits` over a general domain. -/
abbrev CartierDivisorGroup' (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :=
  (FractionalIdeal A⁰ K)ˣ

/-- The principal divisor map (Def 31, Lec 15) sending a unit of `K` to the
fractional ideal it spans; its image is the subgroup of principal divisors. -/
def principalDivisorMap_Def31 (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] : Kˣ →* (FractionalIdeal A⁰ K)ˣ :=
  toPrincipalIdeal A K

/-- The subgroup of principal Cartier divisors, i.e. the image of the principal
divisor map. -/
def PrincipalCartierDivisors (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] : Subgroup (FractionalIdeal A⁰ K)ˣ :=
  (toPrincipalIdeal A K).range

/-- Membership criterion: a Cartier divisor is principal iff some element of `K`
spans it as a singleton fractional ideal. -/
theorem mem_principalCartierDivisors_iff (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (D : (FractionalIdeal A⁰ K)ˣ) :
    D ∈ PrincipalCartierDivisors A K ↔
      ∃ x : K, FractionalIdeal.spanSingleton A⁰ x = (D : FractionalIdeal A⁰ K) :=
  mem_principal_ideals_iff

/-- The Picard group as the quotient `DC / principals`, the abelian group from
Cor 19. -/
abbrev PicardGroupQuot (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] :=
  (FractionalIdeal A⁰ K)ˣ ⧸ PrincipalCartierDivisors A K

end DivisorsPicard

end
