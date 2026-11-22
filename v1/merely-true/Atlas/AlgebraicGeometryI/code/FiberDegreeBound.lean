/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Data.Set.Card

noncomputable section

open Module Ideal

namespace FiberDegreeBound

section Degree

variable (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The degree of a finite morphism of integral domains, defined as the rank of
fraction fields `[K(A) : K(B)]`. -/
def degree : ℕ := finrank (FractionRing B) (FractionRing A)

/-- For a finite extension of domains, `degree` coincides with the module rank. -/
theorem degree_eq_finrank [Module.Finite B A] : degree B A = finrank B A := by
  have : Algebra.IsAlgebraic B A := by
    constructor; intro x; exact (IsIntegral.of_finite B x).isAlgebraic
  exact Algebra.IsAlgebraic.finrank_of_isFractionRing B (FractionRing B) A (FractionRing A)

end Degree

section FiberBoundGeneral

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra



end FiberBoundGeneral

section FiberBound

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S]

/-- Specialization of the fiber bound to Dedekind domains: the number of primes
of `S` lying over a non-zero maximal `p ⊂ R` is at most `[L : K]`. -/
theorem fdb_fiber_card_le_degree
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (primesOverFinset p S).card ≤ finrank K L :=
  Ideal.card_primesOverFinset_le_finrank S K L hp0

omit [NoZeroSMulDivisors R S] in
/-- The fundamental identity `Σ e_i f_i = [L : K]` for primes lying over a
non-zero maximal ideal in a Dedekind extension. -/
theorem fdb_fundamental_identity
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ primesOverFinset p S,
      p.ramificationIdx P * p.inertiaDeg P = finrank K L :=
  Ideal.sum_ramification_inertia S K L hp0

end FiberBound

section UnramifiedGeneral

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- `Spec A → Spec B` is unramified over `𝔭` when the fiber attains the degree
upper bound (i.e. the fiber bound of Lem 13 is an equality). -/
def FdbIsUnramifiedOver (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [NoZeroSMulDivisors B A]
    (𝔭 : Ideal B) : Prop :=
  Nat.card {q : Ideal A | q.IsPrime ∧ q.comap (algebraMap B A) = 𝔭} =
    Module.finrank (FractionRing B) (FractionRing A)

/-- `Spec A → Spec B` is ramified over `𝔭` when the fiber bound is a strict
inequality. -/
def FdbIsRamifiedOver (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [NoZeroSMulDivisors B A]
    (𝔭 : Ideal B) : Prop :=
  ¬ FdbIsUnramifiedOver B A 𝔭

end UnramifiedGeneral

section UnramifiedRamified

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {S : Type*} [CommRing S] [IsDedekindDomain S]
variable [Algebra R S] [NoZeroSMulDivisors R S]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S]

/-- Dedekind-domain version of unramifiedness: the number of primes over `p`
equals `[L : K]`. -/
def FdbIsUnramifiedAt (p : Ideal R) [p.IsMaximal] : Prop :=
  (primesOverFinset p S).card = finrank K L

/-- The Dedekind-domain ramified condition: the fiber bound at `p` is strict. -/
def FdbIsRamifiedAt (p : Ideal R) [p.IsMaximal] : Prop :=
  ¬FdbIsUnramifiedAt (S := S) K L p

/-- Ramification at `p` is equivalent to a strict inequality in the fiber bound. -/
theorem fdb_isRamifiedAt_iff {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    FdbIsRamifiedAt (S := S) K L p ↔ (primesOverFinset p S).card < finrank K L := by
  unfold FdbIsRamifiedAt FdbIsUnramifiedAt
  constructor
  · intro h
    exact lt_of_le_of_ne (Ideal.card_primesOverFinset_le_finrank S K L hp0) h
  · intro h
    exact Nat.ne_of_lt h

/-- If `p` is unramified (fiber bound is an equality), then every `e_P · f_P = 1`,
i.e. `e_P = f_P = 1` for each prime `P` over `p`. -/
theorem fdb_unramified_implies_all_ef_one {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥)
    (hunr : FdbIsUnramifiedAt (S := S) K L p) :
    ∀ P ∈ primesOverFinset p S,
      p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1 := by
  unfold FdbIsUnramifiedAt at hunr
  have hfund := sum_ramification_inertia S K L hp0
  rw [← hunr] at hfund

  have hge1 : ∀ P ∈ primesOverFinset p S,
      1 ≤ p.ramificationIdx P * p.inertiaDeg P := by
    intro P hP
    have hPprime : P.IsPrime := ((mem_primesOverFinset_iff hp0 _).mp hP).1
    have hPover : P.LiesOver p := ((mem_primesOverFinset_iff hp0 _).mp hP).2
    have he : 0 < p.ramificationIdx P :=
      Nat.pos_of_ne_zero (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0)
    have hf : 0 < p.inertiaDeg P := inertiaDeg_pos p P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

  have hall : ∀ P ∈ primesOverFinset p S,
      p.ramificationIdx P * p.inertiaDeg P = 1 := by
    intro P hP
    by_contra h
    have hlt : 1 < p.ramificationIdx P * p.inertiaDeg P :=
      Nat.lt_of_le_of_ne (hge1 P hP) (Ne.symm h)
    have : ∑ Q ∈ primesOverFinset p S, (1 : ℕ) <
        ∑ Q ∈ primesOverFinset p S,
          (p.ramificationIdx Q * p.inertiaDeg Q) :=
      Finset.sum_lt_sum hge1 ⟨P, hP, hlt⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega

  intro P hP
  have h1 := hall P hP
  exact ⟨Nat.eq_one_of_mul_eq_one_right h1, Nat.eq_one_of_mul_eq_one_left h1⟩

omit [NoZeroSMulDivisors R S] in
/-- Converse: if every prime over `p` has `e = f = 1`, then `p` is unramified. -/
theorem fdb_all_ef_one_implies_unramified {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥)
    (hef : ∀ P ∈ primesOverFinset p S,
      p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1) :
    FdbIsUnramifiedAt (S := S) K L p := by
  unfold FdbIsUnramifiedAt
  have hfund := sum_ramification_inertia S K L hp0
  have hone : ∑ P ∈ primesOverFinset p S,
      p.ramificationIdx P * p.inertiaDeg P =
    ∑ P ∈ primesOverFinset p S, 1 := by
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P hP
    simp [he, hf]
  rw [hone, Finset.sum_const, smul_eq_mul, mul_one] at hfund
  exact hfund

/-- Characterization: `p` is unramified iff every prime over `p` has trivial
ramification index and inertia degree. -/
theorem fdb_isUnramifiedAt_iff {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    FdbIsUnramifiedAt (S := S) K L p ↔
    ∀ P ∈ primesOverFinset p S,
      p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1 :=
  ⟨fdb_unramified_implies_all_ef_one K L hp0, fdb_all_ef_one_implies_unramified K L hp0⟩

/-- Each inertia degree `f_P` is bounded by the global degree `[L : K]`. -/
theorem fdb_inertiaDeg_le_degree
    {p : Ideal R} [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hp0 : p ≠ ⊥) :
    inertiaDeg p P ≤ finrank K L :=
  Ideal.inertiaDeg_le_finrank S K L P hp0

/-- Each ramification index `e_P` is bounded by the global degree `[L : K]`. -/
theorem fdb_ramificationIdx_le_degree
    {p : Ideal R} [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    p.ramificationIdx P ≤ finrank K L :=
  Ideal.ramificationIdx_le_finrank S K L P

end UnramifiedRamified

end FiberDegreeBound
