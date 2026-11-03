/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation

open IsDedekindDomain WithZero

/-- Auxiliary lemma: no element of `Multiplicative ℤ` can satisfy `b'.toAdd ≤ -n` for every
natural number $n$, since taking $n$ large enough produces a contradiction. -/
lemma aux_false_of_forall_le_neg_nat (b' : Multiplicative ℤ)
    (h : ∀ n : ℕ, b'.toAdd ≤ -(n : ℤ)) : False := by
  have key := h ((-b'.toAdd + 1).toNat)
  revert key; generalize b'.toAdd = y; omega

/-- Two non-positive integers $x, y$ are equal whenever they satisfy the same family of inequalities
$x \le -n \iff y \le -n$ for all $n \in \mathbb{N}$. -/
lemma aux_eq_of_iff_le_neg_nat (x y : ℤ) (hx : x ≤ 0) (hy : y ≤ 0)
    (h : ∀ n : ℕ, x ≤ -(n : ℤ) ↔ y ≤ -(n : ℤ)) : x = y := by
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
  · exact absurd ((h (-x).toNat).mp (by omega)) (by omega)
  · exact absurd ((h (-y).toNat).mpr (by omega)) (by omega)

/-- Two elements $a, b \le 1$ of $\mathbb{Z}^{\mathrm{m}\circ}$ are equal iff they admit the
same family of upper bounds $a \le \exp(-n) \iff b \le \exp(-n)$ for all natural $n$. -/
lemma WithZero.eq_of_le_exp_neg_iff {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ)) ↔ b ≤ exp (-(n : ℤ))) : a = b := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | coe b' =>
      exfalso
      apply aux_false_of_forall_le_neg_nat b'
      intro n
      have h1 := (h n).mp (WithZero.zero_le _)
      rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
          coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at h1
      exact h1
  | coe a' =>
    cases b with
    | zero =>
      exfalso
      apply aux_false_of_forall_le_neg_nat a'
      intro n
      have h1 := (h n).mpr (WithZero.zero_le _)
      rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
          coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at h1
      exact h1
    | coe b' =>
      congr 1
      have ha' : a'.toAdd ≤ 0 := by
        rw [show (1 : ℤᵐ⁰) = ↑(Multiplicative.ofAdd (0 : ℤ)) from rfl,
            coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at ha
        exact ha
      have hb' : b'.toAdd ≤ 0 := by
        rw [show (1 : ℤᵐ⁰) = ↑(Multiplicative.ofAdd (0 : ℤ)) from rfl,
            coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at hb
        exact hb
      have h' : ∀ n : ℕ, a'.toAdd ≤ -(n : ℤ) ↔ b'.toAdd ≤ -(n : ℤ) := by
        intro n
        constructor
        · intro ha_n
          have : (a' : ℤᵐ⁰) ≤ exp (-(n : ℤ)) := by
            rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
                coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd]
            exact ha_n
          have h1 := (h n).mp this
          rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
              coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at h1
          exact h1
        · intro hb_n
          have : (b' : ℤᵐ⁰) ≤ exp (-(n : ℤ)) := by
            rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
                coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd]
            exact hb_n
          have h1 := (h n).mpr this
          rw [show exp (-(n : ℤ)) = (↑(Multiplicative.ofAdd (-(n : ℤ))) : ℤᵐ⁰) from rfl,
              coe_le_coe, ← Multiplicative.toAdd_le, toAdd_ofAdd] at h1
          exact h1
      rw [← ofAdd_toAdd a', ← ofAdd_toAdd b', aux_eq_of_iff_le_neg_nat _ _ ha' hb' h']


/-- For a ring automorphism $e$ of a Dedekind domain $R$ and a height-one prime $v$,
an element $r$ lies in $(\mathrm{equivOfRingEquiv}\,e\,v)^n$ iff $e^{-1}(r)$ lies in $v^n$. -/
lemma mem_equivOfRingEquiv_pow_iff {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (e : R ≃+* R) (v : HeightOneSpectrum R) (r : R) (n : ℕ) :
    r ∈ (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal ^ n ↔
    e.symm r ∈ v.asIdeal ^ n := by
  have hasideal : (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal := by
    rw [HeightOneSpectrum.equivOfRingEquiv_apply, HeightOneSpectrum.comap_asIdeal]
    exact Ideal.comap_symm e
  rw [hasideal, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]

/-- Compatibility of the $v$-adic integer valuation with a ring automorphism: the valuation at
the transported prime $\mathrm{equivOfRingEquiv}\,e\,v$ applied to $r$ equals the original
valuation at $v$ applied to $e^{-1}(r)$. -/
lemma intValuation_equivOfRingEquiv {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (e : R ≃+* R) (v : HeightOneSpectrum R) (r : R) :
    v.intValuation (e.symm r) =
    (HeightOneSpectrum.equivOfRingEquiv e v).intValuation r := by
  apply WithZero.eq_of_le_exp_neg_iff (HeightOneSpectrum.intValuation_le_one v _)
    (HeightOneSpectrum.intValuation_le_one (HeightOneSpectrum.equivOfRingEquiv e v) _)
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact (mem_equivOfRingEquiv_pow_iff e v r n).symm
