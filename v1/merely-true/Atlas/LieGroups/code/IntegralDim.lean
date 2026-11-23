/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic

open Order

lemma exists_lifted_prime_chain
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hker : RingHom.ker (algebraMap R S) = ⊥)
    (n : ℕ) (s : LTSeries (PrimeSpectrum R)) (hs : s.length = n) :
    ∃ t : LTSeries (PrimeSpectrum S),
      t.length = n ∧
      (t.last).asIdeal.comap (algebraMap R S) = (s.last).asIdeal := by
  induction n generalizing s with
  | zero =>
    have hp := (s.last).2
    obtain ⟨Q, -, hQp, hQeq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (s.last).asIdeal (⊥ : Ideal S)
      (by rw [Ideal.comap_bot_of_injective _
            ((RingHom.injective_iff_ker_eq_bot _).mpr hker)]
          exact bot_le)
    exact ⟨⟨0, ![⟨Q, hQp⟩], fun i => Fin.elim0 i⟩,
           rfl, by simpa [RelSeries.last] using hQeq⟩
  | succ n ih =>
    have hlen_pos : s.length ≠ 0 := by omega
    let s' := s.eraseLast
    have hs'_len : s'.length = n := by simp [s', RelSeries.eraseLast, hs]
    obtain ⟨t', ht'_len, ht'_comap⟩ := ih s' hs'_len
    have hlt_chain : s'.last < s.last := s.eraseLast_last_rel_last hlen_pos
    have hcomap_le : (t'.last).asIdeal.comap (algebraMap R S) ≤ (s.last).asIdeal := by
      rw [ht'_comap]; exact le_of_lt hlt_chain
    have hp := (s.last).2
    obtain ⟨Qnew, hQge, hQp, hQeq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (s.last).asIdeal (t'.last).asIdeal hcomap_le
    have hlt_new : t'.last < (⟨Qnew, hQp⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne hQge ?_
      intro heq
      have heq' : (t'.last).asIdeal = Qnew := PrimeSpectrum.ext_iff.mp heq
      rw [← heq'] at hQeq
      rw [ht'_comap] at hQeq
      exact absurd (PrimeSpectrum.ext_iff.mpr hQeq) (ne_of_lt hlt_chain)
    refine ⟨t'.snoc ⟨Qnew, hQp⟩ hlt_new, ?_, ?_⟩
    · simp [RelSeries.snoc, RelSeries.append, RelSeries.singleton, ht'_len]
    · rw [RelSeries.last_snoc]; exact hQeq
