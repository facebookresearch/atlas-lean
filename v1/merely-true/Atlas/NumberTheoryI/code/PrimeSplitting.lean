/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Over

open Ideal Module

noncomputable section


section DivisibilityLiesOver

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B]

theorem liesOver_of_dvd_map {p : Ideal A} {P : Ideal B}
    [hp : p.IsMaximal] [hP : P.IsPrime]
    (hdvd : P ∣ Ideal.map (algebraMap A B) p) : P.LiesOver p := by
  constructor

  have hle : Ideal.map (algebraMap A B) p ≤ P := Ideal.dvd_iff_le.mp hdvd

  have hle' : p ≤ P.under A := Ideal.map_le_iff_le_comap.mp hle

  have hne : P.under A ≠ ⊤ := Ideal.comap_ne_top (algebraMap A B) hP.ne_top

  exact hp.eq_of_le hne hle'

theorem dvd_map_of_liesOver {p : Ideal A} {P : Ideal B}
    [hlo : P.LiesOver p] : P ∣ Ideal.map (algebraMap A B) p := by
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  exact hlo.over.le

theorem dvd_map_iff_liesOver {p : Ideal A} {P : Ideal B}
    [hp : p.IsMaximal] [hP : P.IsPrime] :
    P ∣ Ideal.map (algebraMap A B) p ↔ P.LiesOver p :=
  ⟨liesOver_of_dvd_map, fun h => by haveI := h; exact dvd_map_of_liesOver⟩

end DivisibilityLiesOver


section RamificationInertiaDef

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] [Algebra A B]

theorem ramificationIdx_def (p : Ideal A) (P : Ideal B) :
    Ideal.ramificationIdx p P = sSup {n | Ideal.map (algebraMap A B) p ≤ P ^ n} :=
  rfl

theorem inertiaDeg_def (p : Ideal A) (P : Ideal B) [P.LiesOver p] :
    Ideal.inertiaDeg p P = finrank (A ⧸ p) (B ⧸ P) :=
  Ideal.inertiaDeg_algebraMap p P

end RamificationInertiaDef


section TowerRamification

variable {A : Type*} [CommRing A] [IsDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable {C : Type*} [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

theorem ramificationIdx_mul_tower
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    Ideal.ramificationIdx p Q =
      Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q :=
  Ideal.ramificationIdx_algebra_tower' p P Q

end TowerRamification

section TowerInertia

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B]
variable {C : Type*} [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

theorem inertiaDeg_mul_tower
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [Q.LiesOver P] :
    Ideal.inertiaDeg p Q =
      Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
  Ideal.inertiaDeg_algebra_tower p P Q

end TowerInertia

section TowerMultiplicativity

variable {A : Type*} [CommRing A] [IsDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable {C : Type*} [CommRing C] [IsDedekindDomain C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

theorem ramificationIdx_inertiaDeg_mul_tower
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    Ideal.ramificationIdx p Q =
      Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q ∧
    Ideal.inertiaDeg p Q =
      Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
  ⟨Ideal.ramificationIdx_algebra_tower' p P Q,
   Ideal.inertiaDeg_algebra_tower p P Q⟩

@[deprecated ramificationIdx_inertiaDeg_mul_tower (since := "2025-05-04")]
theorem lemma_5_30
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P.IsMaximal] [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    Ideal.ramificationIdx p Q =
      Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q ∧
    Ideal.inertiaDeg p Q =
      Ideal.inertiaDeg p P * Ideal.inertiaDeg P Q :=
  ramificationIdx_inertiaDeg_mul_tower p P Q

end TowerMultiplicativity

section IntegralClosureTower

theorem isIntegralClosure_tower_top
    (A : Type*) [CommRing A]
    (B : Type*) [CommRing B]
    (C : Type*) [CommRing C]
    (M : Type*) [CommRing M]
    [Algebra A B] [Algebra A M] [Algebra B M] [Algebra C M]
    [IsScalarTower A B M]
    [IsIntegralClosure C A M]
    [Algebra.IsIntegral A B] :
    IsIntegralClosure C B M :=
  IsIntegralClosure.tower_top (R := A)

@[deprecated isIntegralClosure_tower_top (since := "2025-05-04")]
theorem lemma_5_30_integral_closure
    (A : Type*) [CommRing A]
    (B : Type*) [CommRing B]
    (C : Type*) [CommRing C]
    (M : Type*) [CommRing M]
    [Algebra A B] [Algebra A M] [Algebra B M] [Algebra C M]
    [IsScalarTower A B M]
    [IsIntegralClosure C A M]
    [Algebra.IsIntegral A B] :
    IsIntegralClosure C B M :=
  isIntegralClosure_tower_top A B C M

end IntegralClosureTower


section QuotientDimension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [Module.Finite R S]

theorem dim_quotient_eq_finrank (p : Ideal R) [p.IsMaximal] :
    finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p) = finrank K L :=
  Ideal.finrank_quotient_map p K L

end QuotientDimension


section FundamentalIdentity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S]

theorem sum_ef_eq_degree {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
        Ideal.ramificationIdx p P * Ideal.inertiaDeg p P = finrank K L :=
  Ideal.sum_ramification_inertia S K L hp0

end FundamentalIdentity


section RamificationBounds

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S]
variable [NoZeroSMulDivisors R S]

omit [Module.Finite R S] in
theorem ramificationIdx_pos {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hp0 : p ≠ ⊥) :
    1 ≤ Ideal.ramificationIdx p P :=
  Nat.pos_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0)

theorem ramificationIdx_le {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Ideal.ramificationIdx p P ≤ finrank K L :=
  Ideal.ramificationIdx_le_finrank S K L P

omit [IsDedekindDomain R] [IsDedekindDomain S] [NoZeroSMulDivisors R S] in
theorem inertiaDeg_pos {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    1 ≤ Ideal.inertiaDeg p P :=
  Ideal.inertiaDeg_pos p P

theorem inertiaDeg_le {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hp0 : p ≠ ⊥) :
    Ideal.inertiaDeg p P ≤ finrank K L :=
  Ideal.inertiaDeg_le_finrank S K L P hp0

theorem card_primes_over_pos {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    1 ≤ Finset.card (primesOverFinset p S) := by
  rw [Finset.one_le_card]
  obtain ⟨⟨Q, hQ⟩⟩ : Nonempty (Ideal.primesOver p S) := Ideal.nonempty_primesOver p
  exact ⟨Q, (mem_primesOverFinset_iff hp0 _).mpr hQ⟩

theorem card_primes_over_le {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Finset.card (primesOverFinset p S) ≤ finrank K L :=
  Ideal.card_primesOverFinset_le_finrank S K L hp0

end RamificationBounds


section SplittingTerminology

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra A B]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra B L] [IsFractionRing B L]
variable [Algebra K L] [Algebra A L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Module.Finite A B]

def IsTotallyRamified (p : Ideal A) (P : Ideal B) : Prop :=
  Ideal.ramificationIdx p P = finrank K L

def IsUnramifiedAt (p : Ideal A) (P : Ideal B) [P.LiesOver p] : Prop :=
  Ideal.ramificationIdx p P = 1 ∧
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P)

def IsInert (p : Ideal A) : Prop :=
  (Ideal.map (algebraMap A B) p).IsPrime ∧
    Ideal.inertiaDeg p (Ideal.map (algebraMap A B) p) = finrank K L

def SplitsCompletely (p : Ideal A) : Prop :=
  Finset.card (primesOverFinset p B) = finrank K L

end SplittingTerminology

end
