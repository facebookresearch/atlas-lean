/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Chapter3

open Finset BigOperators

/-- Discrete orthogonality of complex exponentials: for `k` not divisible by `n`, the
sum of `n`-th roots of unity raised to the `k`-th power vanishes,
`∑_{s=0}^{n-1} e^{2πi k s / n} = 0`. -/
theorem discrete_orthogonality (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : ¬ (↑n : ℤ) ∣ k) :
    ∑ s : Fin n,
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hprim : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn0
  have hterm : ∀ s : Fin n,
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n) =
        ω ^ (k * ↑(s : ℕ)) := by
    intro s; rw [← Complex.exp_int_mul]; congr 1; push_cast; ring
  simp_rw [hterm]
  have hpow : ∀ s : Fin n,
      ω ^ (k * ↑(s : ℕ)) = (ω ^ k) ^ (s : ℕ) := by
    intro s; rw [_root_.zpow_mul, zpow_natCast]
  simp_rw [hpow]
  have hωk : ω ^ k ≠ 1 := by
    intro h; exact hk ((hprim.zpow_eq_one_iff_dvd k).mp h)
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hωk]
  have : (ω ^ k) ^ n = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hprim.pow_eq_one, one_zpow]
  rw [this, sub_self, zero_div]

/-- Real part of the discrete orthogonality relation: for `k` not divisible by `n`,
`∑_{s=0}^{n-1} cos(2π k s / n) = 0`. -/
theorem cos_sum_zero (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : ¬ (↑n : ℤ) ∣ k) :
    ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
  have hre : (∑ s : Fin n, Complex.exp
      (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n)).re = 0 := by
    rw [discrete_orthogonality n hn k hk]; simp
  rw [Complex.re_sum] at hre
  convert hre using 1; apply Finset.sum_congr rfl; intro s _
  set θ : ℝ := 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n
  have : (2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n =
      ↑θ * Complex.I := by simp only [θ]; push_cast; ring
  rw [this, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im]

/-- Imaginary part of the discrete orthogonality relation: for `k` not divisible by `n`,
`∑_{s=0}^{n-1} sin(2π k s / n) = 0`. -/
theorem sin_sum_zero (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hk : ¬ (↑n : ℤ) ∣ k) :
    ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
  have him : (∑ s : Fin n, Complex.exp
      (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n)).im = 0 := by
    rw [discrete_orthogonality n hn k hk]; simp
  rw [Complex.im_sum] at him
  convert him using 1; apply Finset.sum_congr rfl; intro s _
  set θ : ℝ := 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n
  have : (2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n =
      ↑θ * Complex.I := by simp only [θ]; push_cast; ring
  rw [this, Complex.exp_mul_I]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re]

/-- A nonzero integer whose absolute value is strictly less than `n` cannot be divisible by `n`. -/
lemma not_dvd (n : ℕ) (k : ℤ) (hk_ne : k ≠ 0) (hk_abs : k.natAbs < n) :
    ¬ (↑n : ℤ) ∣ k := by
  intro ⟨c, hc⟩
  rcases Int.lt_or_lt_of_ne hk_ne with h | h
  · have hc_neg : c ≤ -1 := by
      by_contra hc_ge; push_neg at hc_ge
      linarith [mul_nonneg (show (0 : ℤ) ≤ n from by omega) (show (0 : ℤ) ≤ c from by omega)]
    have : k.natAbs ≥ n := by
      have hk_le : k ≤ -(n : ℤ) := by nlinarith
      omega
    omega
  · exact absurd (Int.le_of_dvd h ⟨c, hc⟩) (by omega)

/-- The integer cast of `a + b` has absolute value less than `n` whenever `a + b < n`. -/
lemma natAbs_coe_add_coe_lt {a b n : ℕ} (h : a + b < n) :
    ((a : ℤ) + (b : ℤ)).natAbs < n := by
  rw [show (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ) from by push_cast; ring, Int.natAbs_natCast]
  exact h

/-- The integer cast of `a - b` has absolute value less than `n` whenever `a + b < n`. -/
lemma natAbs_coe_sub_coe_lt {a b n : ℕ} (h : a + b < n) :
    ((a : ℤ) - (b : ℤ)).natAbs < n := by omega

/-- The integer `2 * a` has absolute value less than `n` whenever `a + a < n`. -/
lemma natAbs_two_mul_coe_lt {a n : ℕ} (h : a + a < n) :
    (2 * (a : ℤ)).natAbs < n := by omega

/-- Sum of squared cosines on the regular grid equals `n / 2` (using
`cos²θ = (1 + cos 2θ) / 2` and discrete orthogonality), provided `n ∤ 2k`. -/
theorem cos_sq_sum (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : ¬ (↑n : ℤ) ∣ (2 * k)) :
    ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 = (n : ℝ) / 2 := by
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 =
    1 / 2 + Real.cos (2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n) / 2 := by
    intro s
    have h := Real.cos_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have heq : 2 * (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) =
      2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n := by ring
    linarith [heq ▸ h]
  simp_rw [key, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  suffices h : ∑ i : Fin n, Real.cos (2 * Real.pi * (2 * ↑k) * ↑(i : ℕ) / ↑n) / 2 = 0 by
    linarith
  rw [← Finset.sum_div]
  simp_rw [show (2 * ↑k : ℝ) = (↑(2 * k) : ℝ) from by push_cast; ring]
  rw [cos_sum_zero n hn (2 * k) hk, zero_div]

/-- Sum of squared sines on the regular grid equals `n / 2` (using
`sin²θ = (1 - cos 2θ) / 2` and discrete orthogonality), provided `n ∤ 2k`. -/
theorem sin_sq_sum (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : ¬ (↑n : ℤ) ∣ (2 * k)) :
    ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 = (n : ℝ) / 2 := by
  have key : ∀ s : Fin n,
    Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 =
    1 / 2 - Real.cos (2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n) / 2 := by
    intro s
    have hcos := Real.cos_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have heq : 2 * (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) =
      2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n := by ring
    linarith [heq ▸ hcos, Real.sin_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)]
  simp_rw [key, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  suffices h : ∑ i : Fin n, Real.cos (2 * Real.pi * (2 * ↑k) * ↑(i : ℕ) / ↑n) / 2 = 0 by
    linarith
  rw [← Finset.sum_div]
  simp_rw [show (2 * ↑k : ℝ) = (↑(2 * k) : ℝ) from by push_cast; ring]
  rw [cos_sum_zero n hn (2 * k) hk, zero_div]

/-- Cross sum of two distinct cosines on the grid vanishes when neither
`k - k'` nor `k + k'` is divisible by `n` (product-to-sum identity plus orthogonality). -/
theorem cos_cos_cross_sum_zero (n : ℕ) (hn : 0 < n) (k k' : ℤ)
    (hkm : ¬ (↑n : ℤ) ∣ (k - k')) (hkp : ¬ (↑n : ℤ) ∣ (k + k')) :
    ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
      Real.cos (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.cos (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.cos (2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n) +
     Real.cos (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.cos_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.cos_sub (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    cos_sum_zero n hn _ hkm, cos_sum_zero n hn _ hkp, add_zero, zero_div]

/-- Cross sum of two distinct sines on the grid vanishes when neither
`k - k'` nor `k + k'` is divisible by `n`. -/
theorem sin_sin_cross_sum_zero (n : ℕ) (hn : 0 < n) (k k' : ℤ)
    (hkm : ¬ (↑n : ℤ) ∣ (k - k')) (hkp : ¬ (↑n : ℤ) ∣ (k + k')) :
    ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
      Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
  have key : ∀ s : Fin n,
    Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.cos (2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n) -
     Real.cos (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.cos_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.cos_sub (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    cos_sum_zero n hn _ hkm, cos_sum_zero n hn _ hkp, sub_self, zero_div]

/-- Cross sum of a cosine and a sine on the grid vanishes under the appropriate
non-divisibility hypotheses on `k + k'` and `k' - k`. -/
theorem cos_sin_sum_zero (n : ℕ) (hn : 0 < n) (k k' : ℤ)
    (hkp : ¬ (↑n : ℤ) ∣ (k + k')) (habs : (k' - k).natAbs < n) :
    ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
      Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.sin (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n) +
     Real.sin (2 * Real.pi * ↑(k' - k) * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.sin_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.sin_sub (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k' - k) * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 := sin_sum_zero n hn _ hkp
  rcases eq_or_ne (k' - k) 0 with heq | hne
  · simp only [heq, Int.cast_zero, mul_zero, zero_mul, zero_div, Real.sin_zero,
      Finset.sum_const_zero, add_zero] at h1 ⊢
    linarith
  · have h2 := sin_sum_zero n hn _ (not_dvd n _ hne habs)
    linarith

/-- Convenience identity `√2 · a · (√2 · b) = 2 · (a · b)` used to simplify products of
normalized trigonometric basis values. -/
lemma sqrt2_factor (a b : ℝ) :
    Real.sqrt 2 * a * (Real.sqrt 2 * b) = 2 * (a * b) := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have eq : Real.sqrt 2 * a * (Real.sqrt 2 * b) = (Real.sqrt 2 * Real.sqrt 2) * (a * b) := by ring
  rw [eq, h]

/-- The trigonometric design matrix `Φ ∈ ℝ^{n × M}` for the regular grid `X_i = (i-1)/n`
with the standard trigonometric basis: column `0` is the constant `1`, odd columns
correspond to `√2 · cos(2π k X_i)`, and even columns to `√2 · sin(2π k X_i)`. -/
noncomputable def trigDesignMatrix (n M : ℕ) : Matrix (Fin n) (Fin M) ℝ :=
  fun i j =>
    if j.val = 0 then 1
    else if j.val % 2 = 1 then
      Real.sqrt 2 * Real.cos (2 * Real.pi * (↑((j.val + 1) / 2) : ℝ) * ↑(i : ℕ) / ↑n)
    else
      Real.sqrt 2 * Real.sin (2 * Real.pi * (↑(j.val / 2) : ℝ) * ↑(i : ℕ) / ↑n)

/-- Lemma 3.13 of Rigollet: for the regular design `X_i = (i-1)/n` and the trigonometric
basis `{φ_j}`, the design matrix `Φ` satisfies the orthogonality condition `Φᵀ Φ = n · I_M`
for `M ≤ n - 1`. -/
theorem lemma_3_13 (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1) :
    (trigDesignMatrix n M).transpose * (trigDesignMatrix n M) =
      (n : ℝ) • (1 : Matrix (Fin M) (Fin M) ℝ) := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, trigDesignMatrix]

  by_cases hj0 : j.val = 0
  ·
    simp only [hj0, ↓reduceIte, one_mul]
    by_cases hj'0 : j'.val = 0
    ·
      have hjj' : j = j' := Fin.ext (by omega)
      simp [hj'0, ↓reduceIte, hjj', Finset.sum_const, Finset.card_fin]
    ·
      have hjne : j ≠ j' := fun h => hj'0 (by rw [← h]; exact hj0)
      simp only [hjne, ite_false, mul_zero, hj'0, ↓reduceIte]
      by_cases hj'_odd : j'.val % 2 = 1
      · simp only [hj'_odd, ↓reduceIte, ← Finset.mul_sum]
        have h := cos_sum_zero n hn (((j'.val + 1) / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'_odd, ↓reduceIte, ← Finset.mul_sum]
        have h := sin_sum_zero n hn ((j'.val / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
  · by_cases hj_odd : j.val % 2 = 1
    ·
      simp only [hj0, hj_odd, ↓reduceIte, ite_false]
      by_cases hj'0 : j'.val = 0
      ·
        simp only [hj'0, ↓reduceIte, mul_one, ← Finset.mul_sum]
        have hjne : j ≠ j' := fun h => hj0 (by rw [h]; exact hj'0)
        simp only [hjne, ite_false, mul_zero]
        have h := cos_sum_zero n hn (((j.val + 1) / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'0, ↓reduceIte]
        by_cases hj'_odd : j'.val % 2 = 1
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          by_cases hjj' : j = j'
          ·
            subst hjj'; simp only [ite_true]
            have hndvd := not_dvd n (2 * (((j.val + 1) / 2 : ℕ) : ℤ)) (by omega)
              (natAbs_two_mul_coe_lt (by omega : (j.val+1)/2 + (j.val+1)/2 < n))
            have h := cos_sq_sum n hn (((j.val + 1) / 2 : ℕ) : ℤ) hndvd
            simp only [Int.cast_natCast] at h
            simp_rw [show ∀ x : Fin n,
                Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) *
                Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) =
                Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) ^ 2
              from fun x => by ring]
            linarith
          ·
            simp only [hjj', ite_false, mul_zero]
            have hk_ne : (((j.val+1)/2 : ℕ) : ℤ) - (((j'.val+1)/2 : ℕ) : ℤ) ≠ 0 := by
              intro h; exact hjj' (Fin.ext (by omega))
            have hkm := not_dvd n _ hk_ne
              (natAbs_coe_sub_coe_lt (by omega : (j.val+1)/2 + (j'.val+1)/2 < n))
            have hkp := not_dvd n _ (by omega : (((j.val+1)/2 : ℕ) : ℤ) + (((j'.val+1)/2 : ℕ) : ℤ) ≠ 0)
              (natAbs_coe_add_coe_lt (by omega : (j.val+1)/2 + (j'.val+1)/2 < n))
            have h := cos_cos_cross_sum_zero n hn _ _ hkm hkp
            simp only [Int.cast_natCast] at h; linarith
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          have hjne : j ≠ j' := by intro h; subst h; omega
          simp only [hjne, ite_false, mul_zero]
          have hkp := not_dvd n _
            (by omega : (((j.val+1)/2 : ℕ) : ℤ) + ((j'.val/2 : ℕ) : ℤ) ≠ 0)
            (natAbs_coe_add_coe_lt (by omega : (j.val+1)/2 + j'.val/2 < n))
          have habs : (((j'.val/2 : ℕ) : ℤ) - (((j.val+1)/2 : ℕ) : ℤ)).natAbs < n := by omega
          have h := cos_sin_sum_zero n hn _ _ hkp habs
          simp only [Int.cast_natCast] at h; linarith
    ·
      simp only [hj0, hj_odd, ↓reduceIte, ite_false]
      by_cases hj'0 : j'.val = 0
      ·
        simp only [hj'0, ↓reduceIte, mul_one, ← Finset.mul_sum]
        have hjne : j ≠ j' := fun h => hj0 (by rw [h]; exact hj'0)
        simp only [hjne, ite_false, mul_zero]
        have h := sin_sum_zero n hn ((j.val / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'0, ↓reduceIte]
        by_cases hj'_odd : j'.val % 2 = 1
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          have hjne : j ≠ j' := by intro h; subst h; omega
          simp only [hjne, ite_false, mul_zero]

          simp_rw [show ∀ x : Fin n,
              Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) *
              Real.cos (2 * Real.pi * ↑((j'.val + 1) / 2) * ↑↑x / ↑n) =
              Real.cos (2 * Real.pi * ↑((j'.val + 1) / 2) * ↑↑x / ↑n) *
              Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n)
            from fun x => by ring]
          have hkp := not_dvd n _
            (by omega : (((j'.val+1)/2 : ℕ) : ℤ) + ((j.val/2 : ℕ) : ℤ) ≠ 0)
            (natAbs_coe_add_coe_lt (by omega : (j'.val+1)/2 + j.val/2 < n))
          have habs : (((j.val/2 : ℕ) : ℤ) - (((j'.val+1)/2 : ℕ) : ℤ)).natAbs < n := by omega
          have h := cos_sin_sum_zero n hn _ _ hkp habs
          simp only [Int.cast_natCast] at h; linarith
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          by_cases hjj' : j = j'
          ·
            subst hjj'; simp only [ite_true]
            have hndvd := not_dvd n (2 * ((j.val / 2 : ℕ) : ℤ)) (by omega)
              (natAbs_two_mul_coe_lt (by omega : j.val/2 + j.val/2 < n))
            have h := sin_sq_sum n hn ((j.val / 2 : ℕ) : ℤ) hndvd
            simp only [Int.cast_natCast] at h
            simp_rw [show ∀ x : Fin n,
                Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) *
                Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) =
                Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) ^ 2
              from fun x => by ring]
            linarith
          ·
            simp only [hjj', ite_false, mul_zero]
            have hk_ne : ((j.val/2 : ℕ) : ℤ) - ((j'.val/2 : ℕ) : ℤ) ≠ 0 := by
              intro h; exact hjj' (Fin.ext (by omega))
            have hkm := not_dvd n _ hk_ne
              (natAbs_coe_sub_coe_lt (by omega : j.val/2 + j'.val/2 < n))
            have hkp := not_dvd n _
              (by omega : ((j.val/2 : ℕ) : ℤ) + ((j'.val/2 : ℕ) : ℤ) ≠ 0)
              (natAbs_coe_add_coe_lt (by omega : j.val/2 + j'.val/2 < n))
            have h := sin_sin_cross_sum_zero n hn _ _ hkm hkp
            simp only [Int.cast_natCast] at h; linarith

end Chapter3
