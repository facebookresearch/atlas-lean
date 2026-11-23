/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic

set_option maxHeartbeats 800000

open Ideal Module

/-- Arithmetic helper: for a finite sum of natural numbers all at least one,
`∑ (f x - 1) = (∑ f x) - |s|`. -/
lemma DegreeFormula.sum_sub_ones {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ x ∈ s, 1 ≤ f x) :
    s.sum (fun x => f x - 1) = s.sum f - s.card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [Finset.sum_cons, Finset.card_cons]
    have ha : 1 ≤ f a := hf a (Finset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ f x := fun x hx => hf x (Finset.mem_cons.mpr (Or.inr hx))
    rw [ih hs]
    have hle : s.card ≤ s.sum f := by
      calc s.card = s.sum (fun _ => 1) := by simp
      _ ≤ s.sum f := Finset.sum_le_sum (fun x hx => hs x hx)
    have h1 : f a - 1 + (s.sum f - s.card) = f a + s.sum f - s.card - 1 := by omega
    have h2 : f a + s.sum f - (s.card + 1) = f a + s.sum f - s.card - 1 := by omega
    linarith

/-- Corollary 27 (fundamental identity `∑ e_i f_i = n`): for a finite extension `B/A`
of Dedekind domains with fraction fields `L/K` and a nonzero prime `𝔭 ⊂ A`,
`∑_{𝔔 ∣ 𝔭} e(𝔔/𝔭) · f(𝔔/𝔭) = [L : K]`. -/
theorem cor27_fundamental_identity
    {A : Type*} {B : Type*} (K : Type*) (L : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (𝔭 : Ideal A) [h𝔭p : 𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOverFinset 𝔭 B).sum
        (fun 𝔔 => 𝔭.ramificationIdx 𝔔 * 𝔭.inertiaDeg 𝔔) =
      Module.finrank K L := by
  haveI : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭
  exact Ideal.sum_ramification_inertia B K L h𝔭

/-- Specialization of Corollary 27 when all inertia degrees `f(𝔔/𝔭)` are one (e.g. for
a separable extension over an algebraically closed residue field): the total ramification
above `𝔭` equals `[L:K]` minus the number of primes above `𝔭`. -/
theorem cor27_ramification_formula
    {A : Type*} {B : Type*} (K : Type*) (L : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [NoZeroSMulDivisors A B]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (𝔭 : Ideal A) [h𝔭p : 𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hf : ∀ 𝔔 ∈ primesOverFinset 𝔭 B, 𝔭.inertiaDeg 𝔔 = 1) :
    (primesOverFinset 𝔭 B).sum
        (fun 𝔔 => 𝔭.ramificationIdx 𝔔 - 1) =
      Module.finrank K L - (primesOverFinset 𝔭 B).card := by
  haveI : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭
  have hfund := Ideal.sum_ramification_inertia B K L h𝔭
  have hsimp : ∀ 𝔔 ∈ primesOverFinset 𝔭 B,
      𝔭.ramificationIdx 𝔔 * 𝔭.inertiaDeg 𝔔 = 𝔭.ramificationIdx 𝔔 := by
    intro 𝔔 h𝔔; rw [hf 𝔔 h𝔔, Nat.mul_one]
  rw [Finset.sum_congr rfl hsimp] at hfund
  rw [DegreeFormula.sum_sub_ones]
  · omega
  · intro 𝔔 h𝔔
    have hmap : Ideal.map (algebraMap A B) 𝔭 ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot h𝔭
    have h𝔔mem := (mem_primesOverFinset_iff h𝔭 B).mp h𝔔
    have hle : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔔 := by
      rw [Ideal.map_le_iff_le_comap]
      exact h𝔔mem.2.over ▸ le_refl _
    exact Nat.one_le_iff_ne_zero.mpr
      (IsDedekindDomain.ramificationIdx_ne_zero hmap h𝔔mem.1 hle)

/-- Abstract type-class data attached to a complete smooth curve `Spec A`, recording the
degree of its canonical divisor. -/
class CompleteSmoothCurve (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] where
  degCanonical : ℤ

/-- The degree of the ramification divisor over a finite set `S` of primes of `A`,
defined as `∑_{𝔭 ∈ S} ∑_{𝔔 ∣ 𝔭} (e(𝔔/𝔭) - 1)`. -/
noncomputable def degRamificationDivisor
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B]
    [IsDedekindDomain B]
    [Algebra A B]
    (S : Finset (Ideal A)) : ℤ :=
  ↑(S.sum (fun 𝔭 => (primesOverFinset 𝔭 B).sum (fun 𝔔 => 𝔭.ramificationIdx 𝔔 - 1)))


