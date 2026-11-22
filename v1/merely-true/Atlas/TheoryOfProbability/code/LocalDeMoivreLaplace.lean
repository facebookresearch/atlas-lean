/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Floor

open Asymptotics Filter Real Topology Nat

noncomputable section

namespace ProbabilityTheory

/-- The point mass `P(S_n = k) = C(n,k) / 2ⁿ` for a `Binomial(n, 1/2)` random variable `S_n`. -/
def binomProbHalf (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) / (2 : ℝ) ^ n

/-- The Gaussian (local CLT) approximation to `binomProbHalf n k`,
`√(2/(π n)) · exp(-(k - n/2)² / (n/2))`. -/
def gaussianApproxHalf (n : ℕ) (k : ℕ) : ℝ :=
  Real.sqrt (2 / (Real.pi * (n : ℝ))) *
    Real.exp (-(((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)))

/-- The integer index `k = ⌊n/2 + x·√n/2⌋` corresponding to the parameter `x` in the local
DeMoivre–Laplace statement: it picks the lattice point near `n/2 + x √n / 2`, so that
`(2k - n)/√n ≈ x`. -/
def localDMLIndex (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / 2 + x * Real.sqrt (n : ℝ) / 2⌋₊

/-- The index `localDMLIndex x n` tends to infinity as `n → ∞`, for any fixed `x : ℝ`. -/
lemma localDMLIndex_tendsto_atTop (x : ℝ) :
    Tendsto (localDMLIndex x) atTop atTop := by
  apply tendsto_atTop.mpr; intro b; rw [eventually_atTop]
  refine ⟨Nat.ceil (4 * (b : ℝ) + x ^ 2 + 4) + 1, fun n hn => ?_⟩
  simp only [localDMLIndex]
  have h_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_cast : (n : ℝ) ≥ 4 * (b : ℝ) + x ^ 2 + 4 := by
    have h1 : (n : ℝ) ≥ (Nat.ceil (4 * (b : ℝ) + x ^ 2 + 4) : ℝ) + 1 := by exact_mod_cast hn
    linarith [Nat.le_ceil (4 * (b : ℝ) + x ^ 2 + 4)]
  exact Nat.le_floor (by nlinarith [sq_nonneg (Real.sqrt n + x), Real.sq_sqrt h_nn])

/-- The complementary index `n - localDMLIndex x n` also tends to infinity, so both `k` and
`n - k` are eventually arbitrarily large. -/
lemma n_sub_localDMLIndex_tendsto_atTop (x : ℝ) :
    Tendsto (fun n => n - localDMLIndex x n) atTop atTop := by
  apply tendsto_atTop.mpr; intro b; rw [eventually_atTop]
  refine ⟨4 * b + Nat.ceil (x ^ 2) + 4, fun n hn => ?_⟩
  simp only [localDMLIndex]
  by_cases hpos : (n : ℝ) / 2 + x * Real.sqrt n / 2 ≥ 0
  · have h_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_large : (n : ℝ) ≥ 4 * (b : ℝ) + x ^ 2 + 4 := by
      have h1 : (n : ℝ) ≥ (4 * b + Nat.ceil (x ^ 2) + 4 : ℕ) := by exact_mod_cast hn
      push_cast at h1; linarith [Nat.le_ceil (x ^ 2)]
    have hx_bound : x * Real.sqrt n ≤ ((n : ℝ) + x ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt n - x), Real.sq_sqrt h_nn]
    have hfloor_upper : (⌊(n : ℝ) / 2 + x * Real.sqrt n / 2⌋₊ : ℝ) ≤
        (n : ℝ) / 2 + x * Real.sqrt n / 2 := Nat.floor_le hpos
    have h_floor_small : ⌊(n : ℝ) / 2 + x * Real.sqrt n / 2⌋₊ + b + 1 ≤ n := by
      have : (⌊(n : ℝ) / 2 + x * Real.sqrt n / 2⌋₊ : ℝ) + (b : ℝ) + 1 ≤ (n : ℝ) := by
        nlinarith [sq_nonneg x]
      exact_mod_cast this
    omega
  · simp only [Nat.floor_of_nonpos (by linarith : (n : ℝ) / 2 + x * Real.sqrt n / 2 ≤ 0)]
    omega

set_option maxHeartbeats 800000 in
/-- The ratio `localDMLIndex x n / n` tends to `1/2` as `n → ∞`, because the correction
`x √n / 2` is `o(n)`. -/
lemma localDMLIndex_ratio_half (x : ℝ) :
    Tendsto (fun n => (localDMLIndex x n : ℝ) / (n : ℝ)) atTop (nhds (1/2)) := by
  set y := fun n : ℕ => (n : ℝ) / 2 + x * Real.sqrt (n : ℝ) / 2

  have hsqrt_tendsto : Tendsto (fun n : ℕ => x / (2 * Real.sqrt (n : ℝ))) atTop (nhds 0) :=
    ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0:ℝ) < 2)).const_div_atTop x

  have h_upper_tendsto : Tendsto (fun n : ℕ => y n / (n : ℝ)) atTop (nhds (1/2)) := by
    have heq : ∀ᶠ n : ℕ in atTop, y n / (n : ℝ) = 1/2 + x / (2 * Real.sqrt (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by linarith)
      simp only [y]; field_simp
      have h1 : Real.sqrt (↑n) * ((↑n : ℝ) + x * Real.sqrt ↑n) =
          Real.sqrt (↑n) * (↑n : ℝ) + x * (Real.sqrt (↑n) * Real.sqrt (↑n)) := by ring
      rw [hsq] at h1; linarith
    refine (tendsto_congr' heq).mpr ?_
    have h := (tendsto_const_nhds (x := (1:ℝ)/2)).add hsqrt_tendsto
    simp only [add_zero] at h; exact h

  have h_lower_tendsto : Tendsto (fun n : ℕ => (y n - 1) / (n : ℝ)) atTop (nhds (1/2)) := by
    have heq : ∀ᶠ n : ℕ in atTop, (y n - 1) / (n : ℝ) = y n / (n : ℝ) - 1 / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    refine (tendsto_congr' heq).mpr ?_
    have h := h_upper_tendsto.sub tendsto_one_div_atTop_nhds_zero_nat
    simp only [sub_zero] at h; exact h

  have h_y_pos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ y n := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (x ^ 2 + 1))] with n hn
    simp only [y]
    have hn_cast : (n : ℝ) ≥ x ^ 2 + 1 := by
      calc (n : ℝ) ≥ (Nat.ceil (x ^ 2 + 1) : ℝ) := by exact_mod_cast hn
        _ ≥ x ^ 2 + 1 := Nat.le_ceil _
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by linarith [sq_nonneg x]
    nlinarith [Real.sq_sqrt hnn, sq_abs x, sq_nonneg (Real.sqrt (n:ℝ) + x)]

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto ?_ ?_
  ·
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp only [localDMLIndex]
    exact (div_le_div_iff_of_pos_right hnn).mpr (by linarith [Nat.sub_one_lt_floor (y n)])
  ·
    filter_upwards [eventually_gt_atTop 0, h_y_pos] with n hn hy
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp only [localDMLIndex]
    exact (div_le_div_iff_of_pos_right hnn).mpr (by exact_mod_cast Nat.floor_le hy)

/-- Rewriting of `m!` in terms of Mathlib's `Stirling.stirlingSeq`:
`m! = stirlingSeq(m) · √(2m) · (m/e)^m`. -/
lemma factorial_eq_stirlingSeq_mul (m : ℕ) (hm : 0 < m) :
    (m ! : ℝ) = Stirling.stirlingSeq m * Real.sqrt (2 * (m : ℝ)) *
      ((m : ℝ) / Real.exp 1) ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * (m : ℝ)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hpow_pos : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m :=
    pow_pos (div_pos hm_pos (Real.exp_pos 1)) m
  rw [Stirling.stirlingSeq]
  field_simp

/-- Algebraic rewriting of the ratio `binomProbHalf n k / gaussianApproxHalf n k` using
Stirling's formula, separating it into a Stirling-sequence factor, a square-root factor,
a power-of-`n` factor, and an exponential correction. -/
lemma binomProb_div_gaussianApprox_eq (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    binomProbHalf n k / gaussianApproxHalf n k =
    (Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))) *
    Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (k : ℝ) * ((n - k : ℕ) : ℝ))) *
    ((n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * 2 ^ n)) *
    Real.exp (((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)) := by
  have hkn' : k ≤ n := Nat.le_of_lt hkn
  have hnk_pos : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hnk_pos' : (0 : ℝ) < ((n - k : ℕ) : ℝ) := Nat.cast_pos.mpr hnk_pos
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp1_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1

  have hstir_n_pos : (0 : ℝ) < Stirling.stirlingSeq n := by
    have h := Stirling.stirlingSeq'_pos (n - 1)
    rwa [show n - 1 + 1 = n from Nat.sub_one_add_one_eq_of_pos hn] at h
  have hstir_k_pos : (0 : ℝ) < Stirling.stirlingSeq k := by
    have h := Stirling.stirlingSeq'_pos (k - 1)
    rwa [show k - 1 + 1 = k from Nat.sub_one_add_one_eq_of_pos hk] at h
  have hstir_nk_pos : (0 : ℝ) < Stirling.stirlingSeq (n - k) := by
    have h := Stirling.stirlingSeq'_pos (n - k - 1)
    rwa [show n - k - 1 + 1 = n - k from Nat.sub_one_add_one_eq_of_pos hnk_pos] at h

  rw [binomProbHalf, Nat.cast_choose ℝ hkn']

  rw [factorial_eq_stirlingSeq_mul n hn, factorial_eq_stirlingSeq_mul k hk,
      factorial_eq_stirlingSeq_mul (n - k) hnk_pos]

  rw [gaussianApproxHalf]


  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have h2nk_pos : (0 : ℝ) < 2 * ((n - k : ℕ) : ℝ) := by linarith
  have hsq2n : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.mpr h2n_pos
  have hsq2k : (0 : ℝ) < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr h2k_pos
  have hsq2nk : (0 : ℝ) < Real.sqrt (2 * ((n - k : ℕ) : ℝ)) := Real.sqrt_pos.mpr h2nk_pos
  have hne_pos : (0 : ℝ) < (n : ℝ) / Real.exp 1 := _root_.div_pos hn_pos hexp1_pos
  have hke_pos : (0 : ℝ) < (k : ℝ) / Real.exp 1 := _root_.div_pos hk_pos hexp1_pos
  have hnke_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) / Real.exp 1 := _root_.div_pos hnk_pos' hexp1_pos

  have hpow_e_cancel : ((n : ℝ) / Real.exp 1) ^ n /
      (((k : ℝ) / Real.exp 1) ^ k * (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) =
      (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    rw [div_pow, div_pow, div_pow]
    have he_ne : (Real.exp 1 : ℝ) ≠ 0 := ne_of_gt hexp1_pos
    have hek_ne : (Real.exp 1 : ℝ) ^ k ≠ 0 := pow_ne_zero _ he_ne
    have henk_ne : (Real.exp 1 : ℝ) ^ (n - k) ≠ 0 := pow_ne_zero _ he_ne
    have hen_ne : (Real.exp 1 : ℝ) ^ n ≠ 0 := pow_ne_zero _ he_ne
    have hekn : (Real.exp 1 : ℝ) ^ k * (Real.exp 1 : ℝ) ^ (n - k) = (Real.exp 1 : ℝ) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hkn']
    field_simp
    linarith [hekn]


  have hsqrt_simplify : Real.sqrt (2 * (n : ℝ)) /
      (Real.sqrt (2 * (k : ℝ)) * Real.sqrt (2 * ((n - k : ℕ) : ℝ)) *
       Real.sqrt (2 / (Real.pi * (n : ℝ)))) =
      Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (k : ℝ) * ((n - k : ℕ) : ℝ))) := by

    have hLHS_pos : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) /
        (Real.sqrt (2 * (k : ℝ)) * Real.sqrt (2 * ((n - k : ℕ) : ℝ)) *
         Real.sqrt (2 / (Real.pi * (n : ℝ)))) := by
      apply _root_.div_pos hsq2n
      apply mul_pos (mul_pos hsq2k hsq2nk)
      exact Real.sqrt_pos.mpr (_root_.div_pos (by norm_num : (0:ℝ) < 2) (mul_pos hpi_pos hn_pos))
    have hRHS_pos : (0 : ℝ) < Real.sqrt (Real.pi * (n : ℝ) ^ 2 /
        (4 * (k : ℝ) * ((n - k : ℕ) : ℝ))) :=
      Real.sqrt_pos.mpr (by positivity)


    rw [← Real.sqrt_sq (le_of_lt hLHS_pos)]
    congr 1

    rw [div_pow, Real.sq_sqrt (le_of_lt h2n_pos),
        mul_pow, mul_pow, Real.sq_sqrt (le_of_lt h2k_pos),
        Real.sq_sqrt (le_of_lt h2nk_pos),
        Real.sq_sqrt (le_of_lt (_root_.div_pos (by norm_num : (0:ℝ) < 2)
          (mul_pos hpi_pos hn_pos)))]
    field_simp
    ring


  rw [show Real.exp (-(((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2))) =
    (Real.exp (((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)))⁻¹ from Real.exp_neg _]

  have hSn_ne : Stirling.stirlingSeq n ≠ 0 := ne_of_gt hstir_n_pos
  have hSk_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hstir_k_pos
  have hSnk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hstir_nk_pos
  have hsq2n_ne : Real.sqrt (2 * (n : ℝ)) ≠ 0 := ne_of_gt hsq2n
  have hsq2k_ne : Real.sqrt (2 * (k : ℝ)) ≠ 0 := ne_of_gt hsq2k
  have hsq2nk_ne : Real.sqrt (2 * ((n - k : ℕ) : ℝ)) ≠ 0 := ne_of_gt hsq2nk
  have hne_pow_ne : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := ne_of_gt (pow_pos hne_pos n)
  have hke_pow_ne : ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := ne_of_gt (pow_pos hke_pos k)
  have hnke_pow_ne : (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k) ≠ 0 :=
    ne_of_gt (pow_pos hnke_pos (n - k))
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos (by norm_num : (0:ℝ) < 2) n)
  have hsqrt_gauss_ne : Real.sqrt (2 / (Real.pi * (n : ℝ))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (_root_.div_pos (by norm_num : (0:ℝ) < 2) (mul_pos hpi_pos hn_pos)))
  have hexp_ne : Real.exp (((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hsqrt_rhs_ne : Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (k : ℝ) * ((n - k : ℕ) : ℝ))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hn_pow_ne : (n : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos hn_pos n)
  have hk_pow_ne : (k : ℝ) ^ k ≠ 0 := ne_of_gt (pow_pos hk_pos k)
  have hnk_pow_ne : ((n - k : ℕ) : ℝ) ^ (n - k) ≠ 0 := ne_of_gt (pow_pos hnk_pos' (n - k))

  rw [← hsqrt_simplify]


  have hinv_pow : (Real.exp 1)⁻¹ ^ n = (Real.exp 1)⁻¹ ^ k * (Real.exp 1)⁻¹ ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn']


  simp only [div_eq_mul_inv, mul_pow] at *
  rw [hinv_pow] at hne_pow_ne ⊢


  field_simp

set_option maxHeartbeats 800000 in
/-- Third-order Taylor bound for the symmetric entropy expansion:
`|(1+u) log(1+u) + (1-u) log(1-u) - u²| ≤ 6 |u|³` whenever `|u| < 1/2`. Used to control the
deviation of the binomial coefficient from its Gaussian approximation. -/
lemma entropy_residual_bound {u : ℝ} (hu : |u| < 1 / 2) :
    |(1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) - u ^ 2| ≤ 6 * |u| ^ 3 := by
  have hu1 : |u| < 1 := by linarith
  have hminu : |-u| < 1 := by rwa [abs_neg]
  have hRp : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
    have h := Real.abs_log_sub_add_sum_range_le hminu 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    simp only [abs_neg] at h
    convert h using 1
    congr 1; ring
  have hRm : |Real.log (1 - u) + u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
    have h := Real.abs_log_sub_add_sum_range_le hu1 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    convert h using 1
    congr 1; ring
  set Rp := Real.log (1 + u) - u + u ^ 2 / 2
  set Rm := Real.log (1 - u) + u + u ^ 2 / 2
  have hkey : (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) - u ^ 2 =
      (1 + u) * Rp + (1 - u) * Rm := by
    simp only [Rp, Rm]; ring
  rw [hkey]
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp (le_of_lt hu)]
  have h1mu : |1 - u| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp (le_of_lt hu)]
  have h_one_minus_u : (1 : ℝ) - |u| > 0 := by linarith [abs_nonneg u]
  have hR_bound : |u| ^ 3 / (1 - |u|) ≤ 2 * |u| ^ 3 := by
    have h2 : (1 : ℝ) - |u| ≥ 1 / 2 := by linarith [abs_nonneg u]
    have h3 : |u| ^ 3 ≥ 0 := by positivity
    calc |u| ^ 3 / (1 - |u|) ≤ |u| ^ 3 / (1 / 2) := by
          apply div_le_div_of_nonneg_left h3 (by linarith) h2
        _ = 2 * |u| ^ 3 := by ring
  calc |(1 + u) * Rp + (1 - u) * Rm|
      ≤ |(1 + u) * Rp| + |(1 - u) * Rm| := abs_add_le _ _
    _ = |1 + u| * |Rp| + |1 - u| * |Rm| := by rw [abs_mul, abs_mul]
    _ ≤ (3 / 2) * |Rp| + (3 / 2) * |Rm| := by gcongr
    _ ≤ (3 / 2) * (|u| ^ 3 / (1 - |u|)) + (3 / 2) * (|u| ^ 3 / (1 - |u|)) := by gcongr
    _ ≤ (3 / 2) * (2 * |u| ^ 3) + (3 / 2) * (2 * |u| ^ 3) := by gcongr
    _ = 6 * |u| ^ 3 := by ring

set_option maxHeartbeats 800000 in
/-- Eventually, the deviation `|2k - n|` for `k = localDMLIndex x n` is at most `|x| √n + 2`,
since `k = ⌊n/2 + x √n / 2⌋`. -/
lemma localDMLIndex_deviation_bound (x : ℝ) :
    ∀ᶠ n in atTop, |(2 : ℝ) * (localDMLIndex x n : ℝ) - (n : ℝ)| ≤ |x| * Real.sqrt n + 2 := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [localDMLIndex]
  set y := (n : ℝ) / 2 + x * Real.sqrt (↑n) / 2 with hy_def
  have h2y_eq : 2 * y = (n : ℝ) + x * Real.sqrt n := by simp only [y]; ring
  by_cases hy : (0 : ℝ) ≤ y
  · have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    have hfl2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le x, Real.sqrt_nonneg (n : ℝ)]
    · nlinarith [le_abs_self x, Real.sqrt_nonneg (n : ℝ)]
  · have hy' : y < 0 := by push_neg at hy; exact hy
    have hfl : ⌊y⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
    rw [hfl]; simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (n : ℝ) + x * Real.sqrt n < 0 := by nlinarith
    nlinarith [neg_le_abs x, Real.sqrt_nonneg (n : ℝ)]

set_option maxHeartbeats 4000000 in
/-- Identity rewriting the logarithm of the power factor `nⁿ / (kᵏ (n-k)^{n-k} 2ⁿ)` plus the
Gaussian exponent `(k - n/2)² / (n/2)` as `-(n/2) · ((1+u) log(1+u) + (1-u) log(1-u) - u²)`,
where `u = (2k - n)/n`. This combines the log-binomial expansion with the Gaussian correction. -/
lemma log_power_factor_formula (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    let u := ((2 : ℝ) * k - n) / n
    Real.log ((↑n : ℝ) ^ n / ((↑k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * 2 ^ n)) +
      ((↑k : ℝ) - (↑n : ℝ) / 2) ^ 2 / ((↑n : ℝ) / 2) =
    -((↑n : ℝ) / 2) * ((1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) - u ^ 2) := by
  intro u
  have hn : (0 : ℝ) < (↑n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn
  have hk' : (0 : ℝ) < (↑k : ℝ) := by exact_mod_cast hk
  have hnk : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hkn_le : k ≤ n := Nat.le_of_lt hkn
  have hkn_cast : (↑k : ℝ) + ((n - k : ℕ) : ℝ) = (↑n : ℝ) := by
    rw [Nat.cast_sub hkn_le]; linarith
  have h1pu : 1 + u = 2 * (↑k : ℝ) / (↑n : ℝ) := by simp only [u]; field_simp; ring
  have h1mu : 1 - u = 2 * ((n - k : ℕ) : ℝ) / (↑n : ℝ) := by
    simp only [u]; field_simp; linarith [hkn_cast]
  have hlog1pu : Real.log (1 + u) = Real.log 2 + Real.log (↑k : ℝ) - Real.log (↑n : ℝ) := by
    rw [h1pu, Real.log_div (by positivity : (2 : ℝ) * (↑k : ℝ) ≠ 0) hn_ne,
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (↑k : ℝ) ≠ 0)]
  have hlog1mu : Real.log (1 - u) = Real.log 2 + Real.log ((n - k : ℕ) : ℝ) - Real.log (↑n : ℝ) := by
    rw [h1mu, Real.log_div (by positivity : (2 : ℝ) * ((n-k:ℕ) : ℝ) ≠ 0) hn_ne,
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : ((n-k:ℕ) : ℝ) ≠ 0)]
  have hlog_pf : Real.log ((↑n : ℝ) ^ n / ((↑k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * 2 ^ n)) =
      (↑n : ℝ) * Real.log (↑n : ℝ) - (↑k : ℝ) * Real.log (↑k : ℝ) -
      ((n - k : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) - (↑n : ℝ) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity),
        Real.log_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]; ring
  rw [hlog_pf, hlog1pu, hlog1mu]
  rw [show (1 : ℝ) + u = 2 * (↑k : ℝ) / (↑n : ℝ) from h1pu,
      show (1 : ℝ) - u = 2 * ((n - k : ℕ) : ℝ) / (↑n : ℝ) from h1mu]
  have hnu2 : u ^ 2 = ((2 * (↑k : ℝ) - (↑n : ℝ)) / (↑n : ℝ)) ^ 2 := by simp only [u]
  rw [hnu2]; field_simp
  linear_combination (2 * (↑n : ℝ) * Real.log 2 - 2 * (↑n : ℝ) * Real.log (↑n : ℝ)) * hkn_cast

set_option maxHeartbeats 8000000 in
/-- The product of the power factor `nⁿ / (kᵏ (n-k)^{n-k} 2ⁿ)` with the Gaussian correction
`exp((k - n/2)² / (n/2))`, evaluated at `k = localDMLIndex x n`, tends to `1` as `n → ∞`.
This is the key analytic estimate behind the local DeMoivre–Laplace limit theorem. -/
lemma dml_power_factor_tendsto_one (x : ℝ) :
    Tendsto (fun n =>
      let k := localDMLIndex x n
      ((n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * 2 ^ n)) *
      Real.exp (((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2)))
    atTop (nhds 1) := by
  suffices hlog : Tendsto (fun n =>
      let k := localDMLIndex x n
      Real.log ((n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) * 2 ^ n)) +
        ((k : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2))
    atTop (nhds 0) by
    have hexp := Real.tendsto_exp_nhds_zero_nhds_one.comp hlog
    apply hexp.congr'
    filter_upwards [localDMLIndex_tendsto_atTop x |>.eventually (eventually_gt_atTop 0),
                    n_sub_localDMLIndex_tendsto_atTop x |>.eventually (eventually_gt_atTop 0),
                    eventually_gt_atTop 0] with n hk hnk hn
    simp only [Function.comp_def]
    exact (Real.exp_add _ _).trans (by rw [Real.exp_log (by positivity)])
  refine @squeeze_zero_norm' ℕ ℝ _ _ (fun n => 3 * (|x| + 2) ^ 3 / Real.sqrt n) atTop ?_ ?_
  · filter_upwards [localDMLIndex_tendsto_atTop x |>.eventually (eventually_gt_atTop 0),
                    n_sub_localDMLIndex_tendsto_atTop x |>.eventually (eventually_gt_atTop 0),
                    eventually_gt_atTop 0,
                    localDMLIndex_deviation_bound x,
                    eventually_ge_atTop (Nat.ceil (16 * (|x| + 2) ^ 2) + 1)] with n hk hnk hn hdev hlarge
    have hkn : localDMLIndex x n < n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    have hsq := Real.sq_sqrt hn_pos.le
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hformula := log_power_factor_formula n (localDMLIndex x n) (by omega : 0 < localDMLIndex x n) hkn
    simp only [] at hformula ⊢
    rw [hformula]
    set u := ((2 : ℝ) * (localDMLIndex x n : ℝ) - (n : ℝ)) / (n : ℝ)
    have hu_bound : |u| ≤ (|x| * Real.sqrt n + 2) / (n : ℝ) := by
      simp only [u, abs_div, abs_of_pos hn_pos]; exact div_le_div_of_nonneg_right hdev hn_pos.le
    have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1), hsq]
    have hbound2 : (|x| * Real.sqrt n + 2) / (n : ℝ) ≤ (|x| + 2) / Real.sqrt n := by
      rw [div_le_div_iff₀ hn_pos hsqrt_pos]; nlinarith [abs_nonneg x]
    have hsqrt_large : Real.sqrt n ≥ 4 * (|x| + 2) := by
      have : (n : ℝ) ≥ 16 * (|x| + 2) ^ 2 + 1 := by
        have h1 : (n : ℝ) ≥ (Nat.ceil (16 * (|x| + 2) ^ 2) + 1 : ℕ) := by exact_mod_cast hlarge
        have h2 := Nat.le_ceil (16 * (|x| + 2) ^ 2); push_cast at h1; linarith
      nlinarith [sq_nonneg (Real.sqrt n - 4 * (|x| + 2))]
    have hu_half : |u| < 1 / 2 := by
      have h1 : (|x| + 2) / Real.sqrt n ≤ 1 / 4 := by
        rw [div_le_div_iff₀ hsqrt_pos (by norm_num : (0:ℝ) < 4)]; linarith
      linarith [le_trans hu_bound hbound2]
    have hent := entropy_residual_bound hu_half
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : (n : ℝ) / 2 > 0)]
    calc (n : ℝ) / 2 * |(1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) - u ^ 2|
        ≤ (n : ℝ) / 2 * (6 * |u| ^ 3) := by gcongr
      _ ≤ (n : ℝ) / 2 * (6 * ((|x| + 2) / Real.sqrt n) ^ 3) := by
          gcongr; exact le_trans hu_bound hbound2
      _ = 3 * (|x| + 2) ^ 3 / Real.sqrt n := by
          rw [div_pow]; field_simp; nlinarith [hsq]
  · exact tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Companion to `localDMLIndex_ratio_half`: the ratio `(n - k) / n` for `k = localDMLIndex x n`
also tends to `1/2`. -/
lemma n_sub_localDMLIndex_ratio_half (x : ℝ) :
    Tendsto (fun n => ((n - localDMLIndex x n : ℕ) : ℝ) / (n : ℝ)) atTop (nhds (1/2)) := by
  have hfn : ∀ᶠ n in atTop, localDMLIndex x n ≤ n := by
    filter_upwards [(n_sub_localDMLIndex_tendsto_atTop x).eventually (eventually_gt_atTop 0)]
      with n hn; omega
  have heq : ∀ᶠ n in atTop, ((n - localDMLIndex x n : ℕ) : ℝ) / (n : ℝ) =
      1 - (localDMLIndex x n : ℝ) / (n : ℝ) := by
    filter_upwards [hfn, eventually_gt_atTop 0] with n hle hn
    rw [Nat.cast_sub hle]; field_simp
  apply (tendsto_congr' heq).mpr
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (localDMLIndex x n : ℝ) / (n : ℝ)) atTop (nhds (1 - 1/2)) :=
    (tendsto_const_nhds (x := (1:ℝ))).sub (localDMLIndex_ratio_half x)
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 from by ring] using h

set_option maxHeartbeats 3200000 in
/-- The binomial point mass and its Gaussian approximation are asymptotically equivalent along
the sequence `k = localDMLIndex x n`:
`binomProbHalf n k ~ gaussianApproxHalf n k` as `n → ∞`. Combines Stirling's formula with the
power-factor and entropy estimates. -/
theorem binomProbHalf_isEquivalent_gaussianApproxHalf (x : ℝ) :
    (fun n => binomProbHalf n (localDMLIndex x n)) ~[atTop]
    (fun n => gaussianApproxHalf n (localDMLIndex x n)) := by
  rw [isEquivalent_iff_tendsto_one]
  ·

    set F := fun n : ℕ =>
        (Stirling.stirlingSeq n / (Stirling.stirlingSeq (localDMLIndex x n) *
          Stirling.stirlingSeq (n - localDMLIndex x n))) *
        Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (localDMLIndex x n : ℝ) *
          ((n - localDMLIndex x n : ℕ) : ℝ))) *
        ((n : ℝ) ^ n / ((localDMLIndex x n : ℝ) ^ (localDMLIndex x n) *
          ((n - localDMLIndex x n : ℕ) : ℝ) ^ (n - localDMLIndex x n) * 2 ^ n)) *
        Real.exp (((localDMLIndex x n : ℝ) - (n : ℝ) / 2) ^ 2 / ((n : ℝ) / 2))

    suffices hF : Tendsto F atTop (nhds 1) by
      apply hF.congr'
      filter_upwards [eventually_gt_atTop 0,
        (localDMLIndex_tendsto_atTop x).eventually (eventually_gt_atTop 0),
        (n_sub_localDMLIndex_tendsto_atTop x).eventually (eventually_gt_atTop 0)] with n hn hk hnk
      simp only [Pi.div_apply, F]
      exact (binomProb_div_gaussianApprox_eq n (localDMLIndex x n) hn (by omega) (by omega)).symm

    show Tendsto F atTop (nhds 1)

    have hstir : Tendsto (fun n : ℕ => Stirling.stirlingSeq n /
        (Stirling.stirlingSeq (localDMLIndex x n) * Stirling.stirlingSeq (n - localDMLIndex x n)))
      atTop (nhds (Real.sqrt Real.pi / (Real.sqrt Real.pi * Real.sqrt Real.pi))) := by
      apply Filter.Tendsto.div
      · exact Stirling.tendsto_stirlingSeq_sqrt_pi
      · exact (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (localDMLIndex_tendsto_atTop x)).mul
          (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (n_sub_localDMLIndex_tendsto_atTop x))
      · have h : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
        exact mul_ne_zero h h

    have hsqrt : Tendsto (fun n : ℕ =>
        Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (localDMLIndex x n : ℝ) *
          ((n - localDMLIndex x n : ℕ) : ℝ))))
      atTop (nhds (Real.sqrt Real.pi)) := by
      apply Tendsto.sqrt
      have heq2 : ∀ᶠ n : ℕ in atTop, Real.pi * (n : ℝ) ^ 2 /
          (4 * (localDMLIndex x n : ℝ) * ((n - localDMLIndex x n : ℕ) : ℝ)) =
          Real.pi / (4 * ((localDMLIndex x n : ℝ) / (n : ℝ)) *
            (((n - localDMLIndex x n : ℕ) : ℝ) / (n : ℝ))) := by
        filter_upwards [eventually_gt_atTop 0,
          (localDMLIndex_tendsto_atTop x).eventually (eventually_gt_atTop 0),
          (n_sub_localDMLIndex_tendsto_atTop x).eventually (eventually_gt_atTop 0)] with n hn hk hnk
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hk_pos : (0 : ℝ) < (localDMLIndex x n : ℝ) := by exact_mod_cast hk
        have hnk_pos : (0 : ℝ) < ((n - localDMLIndex x n : ℕ) : ℝ) := by exact_mod_cast hnk
        field_simp
      apply (tendsto_congr' heq2).mpr
      have hdenom : Tendsto (fun n : ℕ => 4 * ((localDMLIndex x n : ℝ) / (n : ℝ)) *
          (((n - localDMLIndex x n : ℕ) : ℝ) / (n : ℝ))) atTop (nhds 1) := by
        have h := ((tendsto_const_nhds (x := (4:ℝ))).mul (localDMLIndex_ratio_half x)).mul
                  (n_sub_localDMLIndex_ratio_half x)
        simpa only [show (4 : ℝ) * (1 / 2) * (1 / 2) = 1 from by ring] using h
      have h : Tendsto (fun n : ℕ => Real.pi / (4 * ((localDMLIndex x n : ℝ) / (n : ℝ)) *
          (((n - localDMLIndex x n : ℕ) : ℝ) / (n : ℝ)))) atTop (nhds (Real.pi / 1)) :=
        tendsto_const_nhds.div hdenom (by norm_num)
      rwa [div_one] at h

    have hprod_stir_sqrt : Tendsto (fun n : ℕ =>
        Stirling.stirlingSeq n / (Stirling.stirlingSeq (localDMLIndex x n) *
          Stirling.stirlingSeq (n - localDMLIndex x n)) *
        Real.sqrt (Real.pi * (n : ℝ) ^ 2 / (4 * (localDMLIndex x n : ℝ) *
          ((n - localDMLIndex x n : ℕ) : ℝ))))
      atTop (nhds 1) := by
      have h := hstir.mul hsqrt
      have hlim : Real.sqrt Real.pi / (Real.sqrt Real.pi * Real.sqrt Real.pi) *
          Real.sqrt Real.pi = 1 := by
        have hp : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos; field_simp
      rwa [hlim] at h

    have hfull := hprod_stir_sqrt.mul (dml_power_factor_tendsto_one x)
    rw [mul_one] at hfull
    exact hfull.congr (fun n => by simp only [F]; ring)
  ·
    filter_upwards [Filter.Ioi_mem_atTop 0] with n hn
    simp only [gaussianApproxHalf, Set.mem_Ioi] at hn ⊢
    apply mul_ne_zero
    · exact Real.sqrt_ne_zero'.mpr (div_pos (by norm_num : (0:ℝ) < 2)
        (mul_pos Real.pi_pos (by exact_mod_cast hn)))
    · exact (Real.exp_pos _).ne'

/-- **Local DeMoivre–Laplace limit theorem (`p = 1/2` case).**

If `2k/√(2n) → x`, then `P(S_{2n} = 2k) ∼ (π n)^{-1/2} e^{-x²/2}` for a fair-coin random walk
`S_n`. Equivalently, for any `x ∈ ℝ`, the ratio
`binomProbHalf n (localDMLIndex x n) / gaussianApproxHalf n (localDMLIndex x n) → 1`. -/
theorem local_deMoivreLaplace_half (x : ℝ) :
    Tendsto (fun n => binomProbHalf n (localDMLIndex x n) /
      gaussianApproxHalf n (localDMLIndex x n))
    atTop (nhds 1) := by
  have hequiv := binomProbHalf_isEquivalent_gaussianApproxHalf x
  rw [isEquivalent_iff_tendsto_one] at hequiv
  · exact hequiv
  ·
    filter_upwards [Filter.Ioi_mem_atTop 0] with n hn
    simp only [gaussianApproxHalf, Set.mem_Ioi] at hn ⊢
    apply mul_ne_zero
    · exact Real.sqrt_ne_zero'.mpr (div_pos (by norm_num : (0:ℝ) < 2)
        (mul_pos Real.pi_pos (by exact_mod_cast hn)))
    · exact (Real.exp_pos _).ne'

end ProbabilityTheory
