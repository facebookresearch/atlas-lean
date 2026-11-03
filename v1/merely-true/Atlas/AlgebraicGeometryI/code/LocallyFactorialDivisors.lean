/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.ClassGroup
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

open scoped nonZeroDivisors
open IsDedekindDomain

namespace LocallyFactorialDivisors


/-- A ring `R` is locally factorial if all of its localizations at prime ideals
are unique factorization monoids. -/
def IsLocallyFactorial (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime P)

/-- A height-one prime is a nonzero prime ideal (used for Weil divisors). -/
@[ext]
structure HeightOnePrime (R : Type*) [CommRing R] [IsDomain R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal ≠ ⊥

attribute [instance] HeightOnePrime.isPrime

/-- The group of Weil divisors, formal `ℤ`-linear combinations of height-one primes. -/
abbrev WeilDivisorGroup (R : Type*) [CommRing R] [IsDomain R] :=
  HeightOnePrime R →₀ ℤ

/-- The Cartier divisor group, identified with the unit group of fractional
ideals in the fraction field. -/
abbrev CartierDivisorGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :=
  (FractionalIdeal R⁰ K)ˣ

/-- Identification between `HeightOnePrime` and Mathlib's `HeightOneSpectrum`. -/
def heightOnePrimeEquiv (R : Type*) [CommRing R] [IsDomain R] :
    HeightOnePrime R ≃ IsDedekindDomain.HeightOneSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  invFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

/-- The additive equivalence between the local `WeilDivisorGroup` and the version
indexed by Mathlib's `HeightOneSpectrum`. -/
def weilDivisorEquiv (R : Type*) [CommRing R] [IsDomain R] :
    WeilDivisorGroup R ≃+ (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  Finsupp.domCongr (heightOnePrimeEquiv R)




/-- Every Dedekind domain is locally factorial, since localizations at primes are
DVRs (and DVRs are UFDs). -/
theorem dedekind_isLocallyFactorial (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] : IsLocallyFactorial R := by
  intro P hP
  by_cases hbot : P = ⊥
  ·
    subst hbot
    haveI : Ideal.IsPrime (⊥ : Ideal R) := hP
    exact inferInstance
  ·
    haveI := hP
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hbot _
    exact inferInstance



variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Convert a fractional ideal to a Weil divisor by taking valuations at each
height-one prime. -/
def fractionalIdealToWeil (I : FractionalIdeal R⁰ K) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun v => FractionalIdeal.count K v I)
    (Set.Finite.subset (Filter.eventually_cofinite.mp (I.finite_factors))
      (fun v hv => by simp only [Function.mem_support, Set.mem_setOf_eq] at *; exact hv))

/-- The value of `fractionalIdealToWeil` at a prime `v` is the valuation count. -/
@[simp]
lemma fractionalIdealToWeil_apply (I : FractionalIdeal R⁰ K) (v : HeightOneSpectrum R) :
    (fractionalIdealToWeil K I) v = FractionalIdeal.count K v I := by
  simp [fractionalIdealToWeil, Finsupp.ofSupportFinite]

/-- The Cartier-to-Weil map: send a Cartier divisor (a unit fractional ideal) to
its associated Weil divisor. -/
def cartierToWeil (u : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  fractionalIdealToWeil K (u : FractionalIdeal R⁰ K)

/-- Pointwise formula for `cartierToWeil`. -/
@[simp]
lemma cartierToWeil_apply (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    (cartierToWeil K u) v = FractionalIdeal.count K v (u : FractionalIdeal R⁰ K) := by
  simp [cartierToWeil]


/-- The unit Cartier divisor maps to the zero Weil divisor. -/
theorem cartierToWeil_one :
    cartierToWeil K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
  ext v
  simp [FractionalIdeal.count_one]

/-- `cartierToWeil` is multiplicative: product becomes sum of valuations. -/
theorem cartierToWeil_mul (u₁ u₂ : (FractionalIdeal R⁰ K)ˣ) :
    cartierToWeil K (u₁ * u₂) = cartierToWeil K u₁ + cartierToWeil K u₂ := by
  ext v
  simp only [cartierToWeil_apply, Finsupp.add_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v (Units.ne_zero u₁) (Units.ne_zero u₂)

/-- Inverting a Cartier divisor negates its associated Weil divisor. -/
theorem cartierToWeil_inv (u : (FractionalIdeal R⁰ K)ˣ) :
    cartierToWeil K u⁻¹ = -(cartierToWeil K u) := by
  ext v
  simp only [cartierToWeil_apply, Finsupp.neg_apply, Units.val_inv_eq_inv_val]
  exact FractionalIdeal.count_inv K v (u : FractionalIdeal R⁰ K)


/-- The Cartier-to-Weil map is injective: a fractional ideal is determined by its
collection of valuations. -/
theorem cartierToWeil_injective :
    Function.Injective (cartierToWeil (R := R) K) := by
  intro u₁ u₂ h
  have h1 : (u₁ : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero u₁
  have h2 : (u₂ : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero u₂
  have factored1 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := R) K h1
  have factored2 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := R) K h2
  have counts_eq : ∀ v : HeightOneSpectrum R,
      FractionalIdeal.count K v (u₁ : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (u₂ : FractionalIdeal R⁰ K) := by
    intro v
    have := Finsupp.ext_iff.mp h v
    simp only [cartierToWeil, fractionalIdealToWeil_apply] at this
    exact this
  have val_eq : (u₁ : FractionalIdeal R⁰ K) = (u₂ : FractionalIdeal R⁰ K) := by
    rw [← factored1, ← factored2]
    exact finprod_congr (fun v => by rw [counts_eq v])
  exact Units.val_injective val_eq


/-- Construct a fractional ideal from a Weil divisor by taking the product of
prime power factors. -/
def weilToCartierIdeal (D : HeightOneSpectrum R →₀ ℤ) : FractionalIdeal R⁰ K :=
  D.prod (fun v n => (↑v.asIdeal : FractionalIdeal R⁰ K) ^ n)

/-- A nonzero height-one prime ideal gives a nonzero fractional ideal. -/
lemma height_one_coe_ne_zero (v : HeightOneSpectrum R) :
    (↑v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact v.ne_bot

/-- The fractional ideal coming from a Weil divisor is nonzero. -/
theorem weilToCartierIdeal_ne_zero (D : HeightOneSpectrum R →₀ ℤ) :
    weilToCartierIdeal K D ≠ 0 := by
  unfold weilToCartierIdeal
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr
    (fun v _ => zpow_ne_zero _ (height_one_coe_ne_zero K v))

/-- The Cartier-to-Weil map is surjective: every Weil divisor comes from a Cartier
divisor. -/
theorem cartierToWeil_surjective :
    Function.Surjective (cartierToWeil (R := R) K) := by
  intro D

  let I := weilToCartierIdeal K D
  have hI : I ≠ 0 := weilToCartierIdeal_ne_zero K D

  let u := Units.mk0 I hI
  use u

  ext v
  simp only [cartierToWeil_apply]
  exact FractionalIdeal.count_finsuppProd K v D


/-- On a Dedekind domain, the Cartier-to-Weil map is a bijection. -/
theorem weil_eq_cartier_dedekind :
    Function.Bijective (cartierToWeil (R := R) K) :=
  ⟨cartierToWeil_injective K, cartierToWeil_surjective K⟩


/-- The Cartier-to-Weil map packaged as a monoid homomorphism into the
multiplicative form of the Weil divisor group. -/
def cartierToWeilMonoidHom :
    (FractionalIdeal R⁰ K)ˣ →* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun u := Multiplicative.ofAdd (cartierToWeil K u)
  map_one' := by rw [cartierToWeil_one, ofAdd_zero]
  map_mul' a b := by rw [cartierToWeil_mul, ofAdd_add]

/-- The Cartier-to-Weil map upgraded to a multiplicative equivalence, assuming
local factoriality. -/
def cartierToWeilMulEquiv (_hlf : IsLocallyFactorial R) :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  MulEquiv.ofBijective (cartierToWeilMonoidHom K) <| by
    constructor
    ·
      intro u₁ u₂ h
      exact cartierToWeil_injective K h
    ·
      intro m
      obtain ⟨u, hu⟩ := cartierToWeil_surjective K (Multiplicative.toAdd m)
      exact ⟨u, by simp [cartierToWeilMonoidHom, hu]⟩


/-- Cartier and Weil divisor groups are isomorphic on a Dedekind (locally factorial)
domain. -/
theorem weil_iso_cartier_of_dedekind (hlf : IsLocallyFactorial R) :
    Nonempty (CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :=
  ⟨(cartierToWeilMulEquiv K hlf).trans
    (AddEquiv.toMultiplicative (weilDivisorEquiv R)).symm⟩

end LocallyFactorialDivisors


namespace LocallyFactorialDivisors

/-- The Picard group: Cartier divisors modulo principal Cartier divisors. -/
abbrev PicardGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :=
  CartierDivisorGroup R K ⧸ (toPrincipalIdeal R K).range

/-- The Picard group is naturally isomorphic to the ideal class group. -/
def picard_iso_classGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ClassGroup R ≃* PicardGroup R K :=
  ClassGroup.equiv K

/-- Principal Weil divisors are the image of principal Cartier divisors under the
chosen isomorphism `e`. -/
def PrincipalWeilDivisors (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (e : CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :
    Subgroup (Multiplicative (WeilDivisorGroup R)) :=
  Subgroup.map e.toMonoidHom (toPrincipalIdeal R K).range

/-- The Weil divisor class group, Weil divisors modulo principal Weil divisors. -/
abbrev WeilDivisorClassGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (e : CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :=
  Multiplicative (WeilDivisorGroup R) ⧸ PrincipalWeilDivisors R K e


/-- The Picard group is isomorphic to the Weil divisor class group via `e`. -/
def pic_iso_cl (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (e : CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :
    PicardGroup R K ≃* WeilDivisorClassGroup R K e :=
  QuotientGroup.congr _ _ e rfl


end LocallyFactorialDivisors



