/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.HighDimensionalStatistics.code.Chapter3.Ex_3_8

open MeasureTheory Real Set intervalIntegral Chapter3

set_option maxHeartbeats 1600000


/-- Convert an integral over the closed interval `[0,1]` into the
corresponding `intervalIntegral` notation. -/
lemma Icc_to_ii (f : ℝ → ℝ) :
    ∫ x in Icc (0 : ℝ) 1, f x = ∫ x in (0:ℝ)..1, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- `sin(m · 2π) = 0` for any integer `m`. -/
lemma sin_2pi_m (m : ℤ) : sin (↑m * (2 * π)) = 0 := by
  have := sin_int_mul_pi (2 * m)
  rw [show (↑(2 * m) : ℝ) * π = ↑m * (2 * π) from by push_cast; ring] at this; exact this

/-- `∫₀¹ cos(c x) dx = sin c / c` for `c ≠ 0`. -/
lemma ics (c : ℝ) (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, cos (c * x) = sin c / c := by
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := c) (fun x => cos x) hc
  simp only [zero_mul, one_mul] at h; rw [integral_cos] at h
  rw [show (fun x : ℝ => cos (x * c)) = (fun x : ℝ => cos (c * x)) from by ext; ring_nf] at h
  rw [h]; simp [smul_eq_mul]; ring

/-- `∫₀¹ sin(c x) dx = (1 - cos c) / c` for `c ≠ 0`. -/
lemma iss (c : ℝ) (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, sin (c * x) = (1 - cos c) / c := by
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := c) (fun x => sin x) hc
  simp only [zero_mul, one_mul] at h; rw [integral_sin] at h
  rw [show (fun x : ℝ => sin (x * c)) = (fun x : ℝ => sin (c * x)) from by ext; ring_nf] at h
  rw [h]; simp [smul_eq_mul]; ring

/-- `2π m ≠ 0` whenever the integer `m` is non-zero. -/
lemma two_pi_ne (m : ℤ) (hm : m ≠ 0) : (2 : ℝ) * π * ↑m ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (Int.cast_ne_zero.mpr hm)

/-- For any non-zero integer `m`, `∫₀¹ cos(2π m x) dx = 0`. -/
lemma ic0 (m : ℤ) (hm : m ≠ 0) :
    ∫ x in (0:ℝ)..1, cos (2 * π * m * x) = 0 := by
  rw [ics _ (two_pi_ne m hm), show sin (2 * π * ↑m) = sin (↑m * (2 * π)) by ring, sin_2pi_m]; simp

/-- For any non-zero integer `m`, `∫₀¹ sin(2π m x) dx = 0`. -/
lemma is0 (m : ℤ) (hm : m ≠ 0) :
    ∫ x in (0:ℝ)..1, sin (2 * π * m * x) = 0 := by
  rw [iss _ (two_pi_ne m hm), show cos (2 * π * ↑m) = cos (↑m * (2 * π)) by ring, cos_int_mul_two_pi]; simp

/-- For any non-zero integer `m`, `∫₀¹ cos²(2π m x) dx = 1/2`. -/
lemma ics2 (m : ℤ) (hm : m ≠ 0) :
    ∫ x in (0:ℝ)..1, cos (2 * π * m * x) ^ 2 = 1 / 2 := by
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := 2 * π * m) (fun x => cos x ^ 2) (two_pi_ne m hm)
  simp only [zero_mul, one_mul] at h; rw [integral_cos_sq] at h
  rw [show (fun x : ℝ => cos (x * (2 * π * ↑m)) ^ 2) = (fun x : ℝ => cos (2 * π * ↑m * x) ^ 2) from by ext; ring_nf] at h
  rw [h]; simp only [smul_eq_mul, cos_zero, sin_zero]
  conv_lhs => rw [show (2 : ℝ) * π * ↑m = ↑m * (2 * π) from by ring]
  rw [sin_2pi_m, cos_int_mul_two_pi]; field_simp; ring

/-- For any non-zero integer `m`, `∫₀¹ sin²(2π m x) dx = 1/2`. -/
lemma iss2 (m : ℤ) (hm : m ≠ 0) :
    ∫ x in (0:ℝ)..1, sin (2 * π * m * x) ^ 2 = 1 / 2 := by
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := 2 * π * m) (fun x => sin x ^ 2) (two_pi_ne m hm)
  simp only [zero_mul, one_mul] at h; rw [integral_sin_sq] at h
  rw [show (fun x : ℝ => sin (x * (2 * π * ↑m)) ^ 2) = (fun x : ℝ => sin (2 * π * ↑m * x) ^ 2) from by ext; ring_nf] at h
  rw [h]; simp only [smul_eq_mul, cos_zero, sin_zero]
  conv_lhs => rw [show (2 : ℝ) * π * ↑m = ↑m * (2 * π) from by ring]
  rw [sin_2pi_m, cos_int_mul_two_pi]; field_simp; ring


/-- `φ₁(x) = 1`: the first trigonometric basis function is constant. -/
lemma tb_one (x : ℝ) : trigBasis 1 x = 1 := by simp [trigBasis]

/-- Explicit cosine form of the even-indexed trigonometric basis function:
`φ_{2m}(x) = √2 cos(2π m x)` for `m ≥ 1`. -/
lemma tb_even (m : ℕ) (hm : 0 < m) (x : ℝ) :
    trigBasis (2 * m) x = √2 * cos (2 * π * ↑m * x) := by
  simp [trigBasis, show 2 * m ≠ 0 by omega, show 2 * m ≠ 1 by omega,
        show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]

/-- Explicit sine form of the odd-indexed trigonometric basis function:
`φ_{2m+1}(x) = √2 sin(2π m x)` for `m ≥ 1`. -/
lemma tb_odd (m : ℕ) (hm : 0 < m) (x : ℝ) :
    trigBasis (2 * m + 1) x = √2 * sin (2 * π * ↑m * x) := by
  unfold trigBasis
  simp only [show 2 * m + 1 ≠ 0 from by omega, ↓reduceIte,
             show ¬(2 * m + 1 = 1) from by omega,
             show ¬(2 * m + 1) % 2 = 0 from by omega,
             show (2 * m + 1 - 1) / 2 = m from by omega]

/-- Trichotomy for positive integers: every `j ≥ 1` is either `1`,
`2m` for some `m ≥ 1`, or `2m + 1` for some `m ≥ 1`. -/
lemma nat_tri (j : ℕ) (hj : 0 < j) :
    j = 1 ∨ (∃ m, 0 < m ∧ j = 2 * m) ∨ (∃ m, 0 < m ∧ j = 2 * m + 1) := by
  by_cases h1 : j = 1; · exact Or.inl h1
  right
  by_cases heven : j % 2 = 0
  · left; exact ⟨j / 2, by omega, by omega⟩
  · right; exact ⟨(j - 1) / 2, by omega, by omega⟩


/-- Cross-orthogonality of cosines at distinct positive integer frequencies:
`∫₀¹ cos(2π m x) cos(2π n x) dx = 0` for `m ≠ n`. -/
lemma icc0_nat (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    ∫ x in (0:ℝ)..1, cos (2 * π * ↑m * x) * cos (2 * π * ↑n * x) = 0 := by
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have h_sub_ne : (m : ℤ) - n ≠ 0 := by omega
  have key : (fun x : ℝ => cos (2 * π * ↑m * x) * cos (2 * π * ↑n * x)) =
    fun x => (cos (2 * π * ↑(m - n : ℤ) * x) + cos (2 * π * ↑(m + n : ℤ) * x)) / 2 := by
    ext x
    have h1 := cos_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := cos_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring,
               show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      ic0 _ h_sub_ne, ic0 _ h_sum_ne]; simp


/-- Cross-orthogonality of sines at distinct positive integer frequencies:
`∫₀¹ sin(2π m x) sin(2π n x) dx = 0` for `m ≠ n`. -/
lemma iss0_nat (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    ∫ x in (0:ℝ)..1, sin (2 * π * ↑m * x) * sin (2 * π * ↑n * x) = 0 := by
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have h_sub_ne : (m : ℤ) - n ≠ 0 := by omega
  have key : (fun x : ℝ => sin (2 * π * ↑m * x) * sin (2 * π * ↑n * x)) =
    fun x => (cos (2 * π * ↑(m - n : ℤ) * x) - cos (2 * π * ↑(m + n : ℤ) * x)) / 2 := by
    ext x
    have h1 := cos_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := cos_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring,
               show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      ic0 _ h_sub_ne, ic0 _ h_sum_ne]; simp


/-- Sine-cosine cross-orthogonality on `[0,1]`:
`∫₀¹ sin(2π m x) cos(2π n x) dx = 0` for any positive integers `m, n`. -/
lemma isc0_nat (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∫ x in (0:ℝ)..1, sin (2 * π * ↑m * x) * cos (2 * π * ↑n * x) = 0 := by
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have key : (fun x : ℝ => sin (2 * π * ↑m * x) * cos (2 * π * ↑n * x)) =
    fun x => (sin (2 * π * ↑(m + n : ℤ) * x) + sin (2 * π * ↑(m - n : ℤ) * x)) / 2 := by
    ext x
    have h1 := sin_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := sin_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring,
               show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      is0 _ h_sum_ne]
  by_cases h_sub : (m : ℤ) - n = 0
  · rw [h_sub]; simp
  · rw [is0 _ h_sub]; simp


/-- `L²([0,1])` orthonormality of the trigonometric basis:
`∫_{[0,1]} φⱼ(x) φₖ(x) dx = δⱼₖ` for `j, k ≥ 1`. -/
lemma trigBasis_L2_orthonormal' (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    ∫ x in Icc (0 : ℝ) 1, trigBasis j x * trigBasis k x =
      if j = k then 1 else 0 := by
  rw [Icc_to_ii]
  rcases nat_tri j hj with rfl | ⟨mj, hmj, rfl⟩ | ⟨mj, hmj, rfl⟩ <;>
  rcases nat_tri k hk with rfl | ⟨mk, hmk, rfl⟩ | ⟨mk, hmk, rfl⟩

  · simp_rw [tb_one]; simp [intervalIntegral.integral_const]

  · simp only [show ¬(1 = 2 * mk) from by omega, ite_false]
    simp_rw [tb_one, tb_even mk hmk, one_mul, intervalIntegral.integral_const_mul]
    rw [show (fun x => cos (2 * π * ↑mk * x)) = (fun x => cos (2 * π * (↑(mk:ℤ)) * x)) from by push_cast; rfl]
    rw [ic0 mk (by exact_mod_cast show mk ≠ 0 by omega)]; simp

  · simp only [show ¬(1 = 2 * mk + 1) from by omega, ite_false]
    simp_rw [tb_one, tb_odd mk hmk, one_mul, intervalIntegral.integral_const_mul]
    rw [show (fun x => sin (2 * π * ↑mk * x)) = (fun x => sin (2 * π * (↑(mk:ℤ)) * x)) from by push_cast; rfl]
    rw [is0 mk (by exact_mod_cast show mk ≠ 0 by omega)]; simp

  · simp only [show ¬(2 * mj = 1) from by omega, ite_false]
    simp_rw [tb_even mj hmj, tb_one, mul_one, intervalIntegral.integral_const_mul]
    rw [show (fun x => cos (2 * π * ↑mj * x)) = (fun x => cos (2 * π * (↑(mj:ℤ)) * x)) from by push_cast; rfl]
    rw [ic0 mj (by exact_mod_cast show mj ≠ 0 by omega)]; simp

  · simp_rw [tb_even mj hmj, tb_even mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * cos (2 * π * ↑mj * x) * (√2 * cos (2 * π * ↑mk * x)) =
      √2 * √2 * (cos (2 * π * ↑mj * x) * cos (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul]
    by_cases h : mj = mk
    · subst h; simp only [show 2 * mj = 2 * mj from rfl, ite_true]
      rw [show (fun x : ℝ => cos (2 * π * ↑mj * x) * cos (2 * π * ↑mj * x)) =
        (fun x => cos (2 * π * ↑(mj:ℤ) * x) ^ 2) from by ext x; push_cast; ring]
      rw [ics2 mj (by exact_mod_cast show mj ≠ 0 by omega)]
      rw [Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]; ring
    · simp only [show ¬(2 * mj = 2 * mk) from by omega, ite_false]
      rw [icc0_nat mj mk hmj hmk h]; simp

  · simp only [show ¬(2 * mj = 2 * mk + 1) from by omega, ite_false]
    simp_rw [tb_even mj hmj, tb_odd mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * cos (2 * π * ↑mj * x) * (√2 * sin (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mk * x) * cos (2 * π * ↑mj * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul, isc0_nat mk mj hmk hmj]; simp

  · simp only [show ¬(2 * mj + 1 = 1) from by omega, ite_false]
    simp_rw [tb_odd mj hmj, tb_one, mul_one, intervalIntegral.integral_const_mul]
    rw [show (fun x => sin (2 * π * ↑mj * x)) = (fun x => sin (2 * π * (↑(mj:ℤ)) * x)) from by push_cast; rfl]
    rw [is0 mj (by exact_mod_cast show mj ≠ 0 by omega)]; simp

  · simp only [show ¬(2 * mj + 1 = 2 * mk) from by omega, ite_false]
    simp_rw [tb_odd mj hmj, tb_even mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * sin (2 * π * ↑mj * x) * (√2 * cos (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mj * x) * cos (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul, isc0_nat mj mk hmj hmk]; simp

  · simp_rw [tb_odd mj hmj, tb_odd mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * sin (2 * π * ↑mj * x) * (√2 * sin (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mj * x) * sin (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul]
    by_cases h : mj = mk
    · subst h; simp only [show 2 * mj + 1 = 2 * mj + 1 from rfl, ite_true]
      rw [show (fun x : ℝ => sin (2 * π * ↑mj * x) * sin (2 * π * ↑mj * x)) =
        (fun x => sin (2 * π * ↑(mj:ℤ) * x) ^ 2) from by ext x; push_cast; ring]
      rw [iss2 mj (by exact_mod_cast show mj ≠ 0 by omega)]
      rw [Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]; ring
    · simp only [show ¬(2 * mj + 1 = 2 * mk + 1) from by omega, ite_false]
      rw [iss0_nat mj mk hmj hmk h]; simp
