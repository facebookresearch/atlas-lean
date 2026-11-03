/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.ArithmeticFunctions
import Mathlib.FieldTheory.Finite.Basic

open scoped Classical
open ArithmeticFunction

def ArithFunc.IsDirichletCharModulus (f : ArithFunc) (m : ℕ) : Prop :=
  f.IsTotallyMultiplicative ∧ ArithFunc.IsPeriodic f m ∧ ∀ n : ℕ, f n ≠ 0 ↔ Nat.Coprime m n

lemma ArithFunc.IsPeriodic.iterate {f : ArithFunc} {m : ℕ}
    (hf : ArithFunc.IsPeriodic f m) (k : ℕ) (n : ℕ) :
    f (n + m * k) = f n := by
  induction k with
  | zero => simp
  | succ k ih => rw [show n + m * (k + 1) = (n + m * k) + m from by ring, hf _, ih]

lemma ArithFunc.IsPeriodic.of_dvd {f : ArithFunc} {m m' : ℕ}
    (hfm : ArithFunc.IsPeriodic f m) (h : m ∣ m') :
    ArithFunc.IsPeriodic f m' := by
  obtain ⟨k, rfl⟩ := h; intro n; exact hfm.iterate k n

lemma ArithFunc.IsPeriodic.eq_mod {f : ArithFunc} {m : ℕ}
    (hf_per : ArithFunc.IsPeriodic f m) (a : ℕ) : f a = f (a % m) := by
  conv_lhs => rw [show a = a % m + m * (a / m) from (Nat.mod_add_div a m).symm]
  exact hf_per.iterate (a / m) (a % m)

lemma ArithFunc.IsPeriodic.eq_of_modEq {f : ArithFunc} {m : ℕ}
    (hf_per : ArithFunc.IsPeriodic f m) {a b : ℕ} (h : a ≡ b [MOD m]) :
    f a = f b := by
  rw [hf_per.eq_mod a, hf_per.eq_mod b]; congr 1

lemma ArithFunc.period_pos' {f : ArithFunc}
    (hf : ∃ m, 0 < m ∧ ArithFunc.IsPeriodic f m) :
    0 < ArithFunc.period f := by
  unfold ArithFunc.period; rw [dif_pos hf]; exact (Nat.find_spec hf).1

lemma ArithFunc.period_isPeriodic' {f : ArithFunc}
    (hf : ∃ m, 0 < m ∧ ArithFunc.IsPeriodic f m) :
    ArithFunc.IsPeriodic f (ArithFunc.period f) := by
  unfold ArithFunc.period; rw [dif_pos hf]; exact (Nat.find_spec hf).2

lemma ArithFunc.period_min' {f : ArithFunc} {k : ℕ}
    (hf : ∃ m, 0 < m ∧ ArithFunc.IsPeriodic f m)
    (hk : 0 < k ∧ ArithFunc.IsPeriodic f k) :
    ArithFunc.period f ≤ k := by
  unfold ArithFunc.period; rw [dif_pos hf]; exact Nat.find_min' hf hk

lemma ArithFunc.period_dvd_of_isPeriodic {f : ArithFunc} {m : ℕ}
    (hm : 0 < m) (hfm : ArithFunc.IsPeriodic f m) :
    ArithFunc.period f ∣ m := by
  have hf : ∃ k, 0 < k ∧ ArithFunc.IsPeriodic f k := ⟨m, hm, hfm⟩
  have hp_pos := ArithFunc.period_pos' hf
  have hp_per := ArithFunc.period_isPeriodic' hf
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra h
  have hmod_pos : 0 < m % (ArithFunc.period f) := Nat.pos_of_ne_zero h
  have hmod_per : ArithFunc.IsPeriodic f (m % (ArithFunc.period f)) := by
    intro n
    have h1 : f (n + m % (ArithFunc.period f) +
        (ArithFunc.period f) * (m / (ArithFunc.period f))) =
        f (n + m % (ArithFunc.period f)) :=
      hp_per.iterate (m / (ArithFunc.period f)) (n + m % (ArithFunc.period f))
    have h2 : n + m % (ArithFunc.period f) +
        (ArithFunc.period f) * (m / (ArithFunc.period f)) = n + m := by
      have := Nat.div_add_mod m (ArithFunc.period f); omega
    rw [h2] at h1; rw [hfm n] at h1; exact h1.symm
  linarith [ArithFunc.period_min' hf ⟨hmod_pos, hmod_per⟩,
            Nat.mod_lt m hp_pos]

lemma ArithFunc.nonzero_imp_coprime {f : ArithFunc} {m : ℕ}
    (hf_tm : f.IsTotallyMultiplicative)
    (hm_pos : 0 < m)
    (hf_per : ArithFunc.IsPeriodic f m)
    (hf_min : ∀ k, 0 < k → ArithFunc.IsPeriodic f k → m ≤ k)
    {n : ℕ} (hn : f n ≠ 0) : Nat.Coprime m n := by
  by_contra h
  rw [Nat.Prime.not_coprime_iff_dvd] at h
  obtain ⟨p, hp, hpm, hpn⟩ := h
  have hfp : f p ≠ 0 := by
    intro hfp_eq
    have : f n = f p * f (n / p) := by
      rw [← hf_tm.map_mul]; congr 1; exact (Nat.mul_div_cancel' hpn).symm
    rw [hfp_eq, zero_mul] at this; exact hn this
  have hmp_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm_pos hpm) hp.pos
  have hmp_lt : m / p < m := Nat.div_lt_self hm_pos hp.one_lt
  have hmp_per : ArithFunc.IsPeriodic f (m / p) := by
    intro r
    have h1 : f (r * p) = f r * f p := hf_tm.map_mul r p
    have h2 : f (r * p + m) = f (r * p) := hf_per (r * p)
    have h3 : r * p + m = (r + m / p) * p := by
      rw [Nat.add_mul]; congr 1; exact (Nat.div_mul_cancel hpm).symm
    rw [h3] at h2
    rw [hf_tm.map_mul (r + m / p) p, h1] at h2
    exact mul_right_cancel₀ hfp h2
  linarith [hf_min (m / p) hmp_pos hmp_per]

lemma ArithFunc.coprime_imp_nonzero {f : ArithFunc} {m : ℕ}
    (hf_tm : f.IsTotallyMultiplicative) (hm_pos : 0 < m)
    (hf_per : ArithFunc.IsPeriodic f m)
    {n : ℕ} (hcop : Nat.Coprime m n) : f n ≠ 0 := by
  intro hfn
  have hfn_pow : ∀ k : ℕ, 0 < k → f (n ^ k) = 0 := by
    intro k hk; induction k with
    | zero => omega
    | succ k ih =>
      rw [pow_succ, hf_tm.map_mul]
      by_cases hk' : k = 0
      · simp [hk', hfn]
      · rw [ih (Nat.pos_of_ne_zero hk'), zero_mul]
  have heuler : n ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop.symm
  have htot_pos : 0 < m.totient := Nat.totient_pos.mpr hm_pos
  have hfpow : f (n ^ m.totient) = f 1 := hf_per.eq_of_modEq heuler
  rw [hf_tm.map_one] at hfpow
  rw [hfn_pow m.totient htot_pos] at hfpow
  exact zero_ne_one hfpow

lemma dvd_pow_of_primeFactors_subset {m m' : ℕ} (hm' : m' ≠ 0)
    (hsub : m'.primeFactors ⊆ m.primeFactors) :
    ∃ k : ℕ, m' ∣ m ^ k := by
  use m'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  · have hpdvdm' : p ∣ m' := dvd_trans (dvd_pow_self p hk) hpk
    have hpmem : p ∈ m'.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdm', hm'⟩
    have hpdvdm : p ∣ m := Nat.dvd_of_mem_primeFactors (hsub hpmem)
    have hklem' : k ≤ m' := by
      calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
        _ ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        _ ≤ m' := Nat.le_of_dvd (Nat.pos_of_ne_zero hm') hpk
    exact dvd_trans (Nat.pow_dvd_pow p hklem') (pow_dvd_pow_of_dvd hpdvdm m')

theorem ArithFunc.lemma_18_8 {f : ArithFunc} {m : ℕ}
    (hf_tm : f.IsTotallyMultiplicative)
    (hm_pos : 0 < m)
    (hf_per : ArithFunc.IsPeriodic f m)
    (hf_min : ArithFunc.period f = m)
    (m' : ℕ) (hm'_pos : 0 < m') :
    f.IsDirichletCharModulus m' ↔ (m ∣ m' ∧ ∃ k, m' ∣ m ^ k) := by

  have hf_exists : ∃ k, 0 < k ∧ ArithFunc.IsPeriodic f k := ⟨m, hm_pos, hf_per⟩
  have hperiod_min : ∀ k, 0 < k → ArithFunc.IsPeriodic f k → m ≤ k := by
    intro k hk hfk
    rw [← hf_min]; exact ArithFunc.period_min' hf_exists ⟨hk, hfk⟩
  constructor
  ·
    intro ⟨_, hper', hnonzero⟩
    constructor
    ·
      rw [← hf_min]
      exact ArithFunc.period_dvd_of_isPeriodic hm'_pos hper'
    ·
      apply dvd_pow_of_primeFactors_subset (Nat.pos_iff_ne_zero.mp hm'_pos)
      intro p hp
      rw [Nat.mem_primeFactors] at hp ⊢
      obtain ⟨hpp, hpdvdm', _⟩ := hp
      refine ⟨hpp, ?_, Nat.pos_iff_ne_zero.mp hm_pos⟩


      have hncop_m'p : ¬Nat.Coprime m' p := by
        rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]; exact not_not.mpr hpdvdm'
      have hfp_zero : f p = 0 := by
        by_contra hfp; exact hncop_m'p ((hnonzero p).mp hfp)

      by_contra hpm_not
      have hcop_mp : Nat.Coprime m p := by
        rwa [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      exact (ArithFunc.coprime_imp_nonzero hf_tm hm_pos hf_per hcop_mp) hfp_zero
  ·
    intro ⟨hdvd, hpow⟩
    refine ⟨hf_tm, hf_per.of_dvd hdvd, ?_⟩
    intro n
    constructor
    ·
      intro hfn
      obtain ⟨k, hk⟩ := hpow
      have hcop_m := ArithFunc.nonzero_imp_coprime hf_tm hm_pos hf_per hperiod_min hfn

      exact Nat.Coprime.coprime_dvd_left hk (hcop_m.pow_left k)
    ·
      intro hcop

      have hcop_m : Nat.Coprime m n := Nat.Coprime.coprime_dvd_left hdvd hcop
      exact ArithFunc.coprime_imp_nonzero hf_tm hm_pos hf_per hcop_m
