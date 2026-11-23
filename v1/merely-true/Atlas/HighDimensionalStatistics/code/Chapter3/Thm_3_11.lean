/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10

open Real MeasureTheory Set

namespace Chapter3

/-- The Sobolev ellipsoid `Θ(β, Q)` defined as the set of sequences `θ : ℕ → ℝ`
all of whose finite partial sums `∑ aⱼ² θⱼ²` (with `aⱼ` the Sobolev coefficients)
are bounded by `Q`. -/
def SobolevEllipsoidInf (β Q : ℝ) : Set (ℕ → ℝ) :=
  {θ | ∀ M : ℕ,
    ∑ j : Fin M, (sobolevCoeff β (j.val + 1)) ^ 2 * (θ (j.val + 1)) ^ 2 ≤ Q}

/-- Value of the Sobolev coefficient at an even index: `a_{2k} = (2k)^β`. -/
lemma sobolevCoeff_even (β : ℝ) (k : ℕ) :
    sobolevCoeff β (2 * k) = (2 * k : ℝ) ^ β := by
  unfold sobolevCoeff; simp [Nat.mul_mod_right]

/-- Value of the Sobolev coefficient at an odd index: `a_{2k+1} = (2k)^β`. -/
lemma sobolevCoeff_odd (β : ℝ) (k : ℕ) :
    sobolevCoeff β (2 * k + 1) = (2 * k : ℝ) ^ β := by
  unfold sobolevCoeff; simp


/-- Inductive step: if `iteratedDeriv (k+1) f` is absolutely continuous on `[0,1]`
and `iteratedDeriv k f` has derivative `iteratedDeriv (k+1) f`, then
`iteratedDeriv k f` is also absolutely continuous on `[0,1]`. -/
theorem ac_step_iteratedDeriv (f : ℝ → ℝ) (k : ℕ)
    (hac_succ : AbsolutelyContinuousOnInterval (iteratedDeriv (k + 1) f) 0 1)
    (hdiff : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x) :
    AbsolutelyContinuousOnInterval (iteratedDeriv k f) 0 1 := by
  obtain ⟨C, hC⟩ := hac_succ.exists_bound
  have hC_le : ∀ x ∈ Set.uIcc (0:ℝ) 1, ‖iteratedDeriv (k + 1) f x‖ ≤ max C 0 :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  have hlip : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩
      (iteratedDeriv k f) (Set.uIcc (0:ℝ) 1) := by
    apply (convex_uIcc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    · intro x hx; exact (hdiff x hx).hasDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, NNReal.coe_mk, coe_nnnorm]
      exact hC_le x hx
  exact hlip.absolutelyContinuousOnInterval



/-- The function `x ↦ √2 · cos(c·x)` is absolutely continuous on `[0, 1]`. -/
lemma ac_cos_smul (c : ℝ) : AbsolutelyContinuousOnInterval
    (fun x : ℝ => √2 * cos (c * x)) 0 1 :=
  ((lipschitzWith_smul (√2 : ℝ)).comp
    (lipschitzWith_cos.comp (lipschitzWith_smul c))).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The function `x ↦ √2 · sin(c·x)` is absolutely continuous on `[0, 1]`. -/
lemma ac_sin_smul (c : ℝ) : AbsolutelyContinuousOnInterval
    (fun x : ℝ => √2 * sin (c * x)) 0 1 :=
  ((lipschitzWith_smul (√2 : ℝ)).comp
    (lipschitzWith_sin.comp (lipschitzWith_smul c))).lipschitzOnWith.absolutelyContinuousOnInterval

/-- Every element `φ_k` of the trigonometric basis is absolutely continuous on `[0, 1]`. -/
theorem ac_trigBasis (k : ℕ) : AbsolutelyContinuousOnInterval (trigBasis k) 0 1 := by
  have key : trigBasis k = fun x =>
    if k = 0 then 0
    else if k = 1 then 1
    else if k % 2 = 0 then √2 * cos (2 * π * (k / 2 : ℕ) * x)
    else √2 * sin (2 * π * ((k - 1) / 2 : ℕ) * x) := by
    ext x; simp [trigBasis]
  rw [key]
  split_ifs with h0 h1 heven
  · exact (LipschitzWith.const (0:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  · exact (LipschitzWith.const (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  · exact ac_cos_smul _
  · exact ac_sin_smul _

/-- Derivative of an even basis function: `φ'_{2k}(x) = -(2π k) · φ_{2k+1}(x)`. -/
theorem deriv_trigBasis_even (k : ℕ) (hk : 1 ≤ k) :
    deriv (trigBasis (2 * k)) = fun x => -(2 * π * ↑k) * trigBasis (2 * k + 1) x := by
  ext x

  have heven : trigBasis (2 * k) = fun x => √2 * cos (2 * π * ↑k * x) := by
    ext x; unfold trigBasis
    simp only [show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega, Nat.mul_mod_right, ite_false, ite_true]
    rw [show (2 * k / 2 : ℕ) = k from Nat.mul_div_cancel_left k (by omega)]

  have hodd : trigBasis (2 * k + 1) x = √2 * sin (2 * π * ↑k * x) := by
    unfold trigBasis
    simp only [show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega,
               show (2 * k + 1) % 2 ≠ 0 by omega, ite_false]
    rw [show ((2 * k + 1 - 1) / 2 : ℕ) = k from by omega]
  rw [heven, hodd]

  have hd : HasDerivAt (fun x => √2 * cos (2 * π * ↑k * x))
      (√2 * (-sin (2 * π * ↑k * x) * (2 * π * ↑k))) x := by
    have h_inner : HasDerivAt (fun y => 2 * π * ↑k * y) (2 * π * ↑k) x :=
      hasDerivAt_const_mul (2 * π * ↑k)
    have h_cos : HasDerivAt cos (-sin (2 * π * ↑k * x)) (2 * π * ↑k * x) :=
      hasDerivAt_cos _
    exact (h_cos.comp x h_inner).const_mul √2
  rw [hd.deriv]
  ring

/-- Derivative of an odd basis function: `φ'_{2k+1}(x) = (2π k) · φ_{2k}(x)`. -/
theorem deriv_trigBasis_odd (k : ℕ) (hk : 1 ≤ k) :
    deriv (trigBasis (2 * k + 1)) = fun x => (2 * π * ↑k) * trigBasis (2 * k) x := by
  ext x

  have hodd : trigBasis (2 * k + 1) = fun x => √2 * sin (2 * π * ↑k * x) := by
    ext x; unfold trigBasis
    simp only [show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega,
               show (2 * k + 1) % 2 ≠ 0 by omega, ite_false]
    rw [show ((2 * k + 1 - 1) / 2 : ℕ) = k from by omega]

  have heven : trigBasis (2 * k) x = √2 * cos (2 * π * ↑k * x) := by
    unfold trigBasis
    simp only [show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega, Nat.mul_mod_right, ite_false, ite_true]
    rw [show (2 * k / 2 : ℕ) = k from Nat.mul_div_cancel_left k (by omega)]
  rw [hodd, heven]

  have hd : HasDerivAt (fun x => √2 * sin (2 * π * ↑k * x))
      (√2 * (cos (2 * π * ↑k * x) * (2 * π * ↑k))) x := by
    have h_inner : HasDerivAt (fun y => 2 * π * ↑k * y) (2 * π * ↑k) x :=
      hasDerivAt_const_mul (2 * π * ↑k)
    have h_sin : HasDerivAt sin (cos (2 * π * ↑k * x)) (2 * π * ↑k * x) :=
      hasDerivAt_sin _
    exact (h_sin.comp x h_inner).const_mul √2
  rw [hd.deriv]
  ring

/-- The Fourier coefficient of `iteratedDeriv j f` against `trigBasis k`
equals the corresponding interval integral over `[0, 1]`. -/
lemma derivFourierCoeff_eq_intervalIntegral (f : ℝ → ℝ) (j k : ℕ) :
    derivFourierCoeff f j k = ∫ x in (0:ℝ)..1, iteratedDeriv j f x * trigBasis k x := by
  unfold derivFourierCoeff
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- Boundary value: `φ_{2k}(0) = √2`. -/
lemma trigBasis_even_at_zero (k : ℕ) (hk : 1 ≤ k) : trigBasis (2 * k) 0 = √2 := by
  unfold trigBasis
  simp [show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega, Nat.mul_mod_right]

/-- Boundary value: `φ_{2k}(1) = √2`. -/
lemma trigBasis_even_at_one (k : ℕ) (hk : 1 ≤ k) : trigBasis (2 * k) 1 = √2 := by
  unfold trigBasis
  simp only [show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega,
             Nat.mul_mod_right, ite_false, ite_true, mul_one]
  have : (2 * k / 2 : ℕ) = k := Nat.mul_div_cancel_left k (by omega)
  rw [this, show 2 * π * (k : ℝ) = ↑(k : ℤ) * (2 * π) from by push_cast; ring,
      cos_int_mul_two_pi, mul_one]

/-- Boundary value: `φ_{2k+1}(0) = 0`. -/
lemma trigBasis_odd_at_zero (k : ℕ) (hk : 1 ≤ k) : trigBasis (2 * k + 1) 0 = 0 := by
  unfold trigBasis
  simp only [show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega,
             show (2 * k + 1) % 2 ≠ 0 by omega, ite_false, mul_zero, sin_zero, mul_zero]

/-- Boundary value: `φ_{2k+1}(1) = 0`. -/
lemma trigBasis_odd_at_one (k : ℕ) (hk : 1 ≤ k) : trigBasis (2 * k + 1) 1 = 0 := by
  unfold trigBasis
  simp only [show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega,
             show (2 * k + 1) % 2 ≠ 0 by omega, ite_false, mul_one]
  have : ((2 * k + 1 - 1) / 2 : ℕ) = k := by omega
  rw [this, show 2 * π * (k : ℝ) = ↑(2 * (k : ℤ)) * π from by push_cast; ring,
      sin_int_mul_pi, mul_zero]






/-- Conversion of the integration-by-parts identity into a form using
the Sobolev coefficients `a_j` and `π^(2β)`. -/
theorem fourier_deriv_identity (β : ℝ) (k : ℕ) (_hk : 1 ≤ k)
    (s_even s_odd θ_even θ_odd : ℝ)
    (hIBP : s_even ^ 2 + s_odd ^ 2 =
      (2 * π * k) ^ (2 * β) * (θ_even ^ 2 + θ_odd ^ 2)) :
    s_even ^ 2 + s_odd ^ 2 =
      π ^ (2 * β) * ((sobolevCoeff β (2 * k)) ^ 2 * θ_even ^ 2 +
                      (sobolevCoeff β (2 * k + 1)) ^ 2 * θ_odd ^ 2) := by
  rw [sobolevCoeff_even, sobolevCoeff_odd, hIBP]
  have h2k : (0 : ℝ) ≤ 2 * ↑k := by positivity
  have hsq : ((2 * ↑k : ℝ) ^ β) ^ 2 = (2 * ↑k : ℝ) ^ (2 * β) := by
    rw [← rpow_natCast ((2 * ↑k : ℝ) ^ β) 2, ← rpow_mul h2k]; ring_nf
  rw [hsq, show (2 * π * ↑k : ℝ) = π * (2 * ↑k) from by ring,
      mul_rpow pi_nonneg h2k]
  ring

/-- Orthonormality of the trigonometric basis on `[0, 1]`:
`∫₀¹ φᵢ(x) · φⱼ(x) dx = δᵢⱼ` for `i, j ≥ 1`. -/
theorem trigBasis_orthonormal (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∫ x in Icc (0 : ℝ) 1, trigBasis i x * trigBasis j x =
      if i = j then 1 else 0 := by

  rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

  have int_cos_period : ∀ n : ℤ, n ≠ 0 →
      ∫ x in (0:ℝ)..1, cos (2 * π * ↑n * x) = 0 := by
    intro n hn
    have hc : (2 * π * (↑n : ℝ)) ≠ 0 := by
      apply mul_ne_zero; exact mul_ne_zero two_ne_zero pi_ne_zero; exact_mod_cast hn
    have heq : (fun x : ℝ => cos (2 * π * ↑n * x)) = (fun x => cos ((2 * π * ↑n) * x)) := by
      ext; ring_nf
    rw [heq, intervalIntegral.integral_comp_mul_left _ hc, mul_zero, mul_one, integral_cos,
        show 2 * π * (↑n : ℝ) = ↑(2 * n) * π from by push_cast; ring, sin_int_mul_pi,
        sin_zero, sub_self, smul_zero]
  have int_sin_period : ∀ n : ℤ, n ≠ 0 →
      ∫ x in (0:ℝ)..1, sin (2 * π * ↑n * x) = 0 := by
    intro n hn
    have hc : (2 * π * (↑n : ℝ)) ≠ 0 := by
      apply mul_ne_zero; exact mul_ne_zero two_ne_zero pi_ne_zero; exact_mod_cast hn
    have heq : (fun x : ℝ => sin (2 * π * ↑n * x)) = (fun x => sin ((2 * π * ↑n) * x)) := by
      ext; ring_nf
    rw [heq, intervalIntegral.integral_comp_mul_left _ hc, mul_zero, mul_one, integral_sin]
    simp only [show 2 * π * (↑n : ℝ) = ↑n * (2 * π) from by ring, cos_int_mul_two_pi,
      cos_zero, sub_self, smul_zero]

  have int_cos_cos : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ x in (0:ℝ)..1, cos (2 * π * ↑a * x) * cos (2 * π * ↑b * x) =
        if a = b then 1/2 else 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => cos (2 * π * ↑a * x) * cos (2 * π * ↑b * x)) =
        (fun x => (cos (2 * π * (↑a - ↑b : ℤ) * x) + cos (2 * π * (↑a + ↑b : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_cos_mul_cos (2 * π * ↑a * x) (2 * π * ↑b * x)
      have h1 : cos (2 * π * (↑a - ↑b : ℤ) * x) = cos (2 * π * ↑a * x - 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      have h2 : cos (2 * π * (↑a + ↑b : ℤ) * x) = cos (2 * π * ↑a * x + 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
        intervalIntegral.integral_add
          ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _),
        int_cos_period _ (by omega : (↑a + ↑b : ℤ) ≠ 0), add_zero]
    split_ifs with h
    · subst h; simp [sub_self, intervalIntegral.integral_const]
    · rw [int_cos_period _ (by omega : (↑a - ↑b : ℤ) ≠ 0), zero_div]
  have int_sin_sin : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ x in (0:ℝ)..1, sin (2 * π * ↑a * x) * sin (2 * π * ↑b * x) =
        if a = b then 1/2 else 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => sin (2 * π * ↑a * x) * sin (2 * π * ↑b * x)) =
        (fun x => (cos (2 * π * (↑a - ↑b : ℤ) * x) - cos (2 * π * (↑a + ↑b : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_sin_mul_sin (2 * π * ↑a * x) (2 * π * ↑b * x)
      have h1 : cos (2 * π * (↑a - ↑b : ℤ) * x) = cos (2 * π * ↑a * x - 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      have h2 : cos (2 * π * (↑a + ↑b : ℤ) * x) = cos (2 * π * ↑a * x + 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
        intervalIntegral.integral_sub
          ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _),
        int_cos_period _ (by omega : (↑a + ↑b : ℤ) ≠ 0), sub_zero]
    split_ifs with h
    · subst h; simp [sub_self, intervalIntegral.integral_const]
    · rw [int_cos_period _ (by omega : (↑a - ↑b : ℤ) ≠ 0), zero_div]
  have int_cos_sin : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ x in (0:ℝ)..1, cos (2 * π * ↑a * x) * sin (2 * π * ↑b * x) = 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => cos (2 * π * ↑a * x) * sin (2 * π * ↑b * x)) =
        (fun x => (sin (2 * π * (↑b - ↑a : ℤ) * x) + sin (2 * π * (↑b + ↑a : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_sin_mul_cos (2 * π * ↑b * x) (2 * π * ↑a * x)
      have h1 : sin (2 * π * (↑b - ↑a : ℤ) * x) = sin (2 * π * ↑b * x - 2 * π * ↑a * x) := by
        congr 1; push_cast; ring
      have h2 : sin (2 * π * (↑b + ↑a : ℤ) * x) = sin (2 * π * ↑b * x + 2 * π * ↑a * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
        intervalIntegral.integral_add
          ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    by_cases hab : (↑b - ↑a : ℤ) = 0
    · rw [int_sin_period _ (by omega : (↑b + ↑a : ℤ) ≠ 0)]
      simp only [hab, Int.cast_zero, mul_zero, zero_mul, sin_zero,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul, zero_add, zero_div]
    · rw [int_sin_period _ hab, int_sin_period _ (by omega : (↑b + ↑a : ℤ) ≠ 0),
          zero_add, zero_div]
  have int_sin_cos : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ x in (0:ℝ)..1, sin (2 * π * ↑a * x) * cos (2 * π * ↑b * x) = 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => sin (2 * π * ↑a * x) * cos (2 * π * ↑b * x)) =
      (fun x => cos (2 * π * ↑b * x) * sin (2 * π * ↑a * x)) := by ext x; ring
    rw [heq, int_cos_sin b a hb ha]

  have sqrt2_sq : (√2 : ℝ) * √2 = 2 := by rw [← sq, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]

  rcases Nat.eq_or_lt_of_le hi with rfl | hi2
  ·
    rcases Nat.eq_or_lt_of_le hj with rfl | hj2
    ·
      simp [trigBasis_one, intervalIntegral.integral_const]
    ·
      simp only [show (1 : ℕ) ≠ j by omega, ite_false, trigBasis_one, one_mul]
      unfold trigBasis
      simp only [show j ≠ 0 by omega, show j ≠ 1 by omega, ite_false]
      split_ifs with hje
      · rw [intervalIntegral.integral_const_mul,
            show (↑(j / 2 : ℕ) : ℝ) = ((↑(j / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
            int_cos_period ↑(j / 2 : ℕ) (by omega), mul_zero]
      · rw [intervalIntegral.integral_const_mul,
            show (↑((j - 1) / 2 : ℕ) : ℝ) = ((↑((j - 1) / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
            int_sin_period ↑((j - 1) / 2 : ℕ) (by omega), mul_zero]
  ·
    rcases Nat.eq_or_lt_of_le hj with rfl | hj2
    ·
      simp only [show i ≠ 1 by omega, ite_false, trigBasis_one]
      unfold trigBasis
      simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, ite_false]
      split_ifs with hie
      · simp only [mul_one]
        rw [intervalIntegral.integral_const_mul,
            show (↑(i / 2 : ℕ) : ℝ) = ((↑(i / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
            int_cos_period ↑(i / 2 : ℕ) (by omega), mul_zero]
      · simp only [mul_one]
        rw [intervalIntegral.integral_const_mul,
            show (↑((i - 1) / 2 : ℕ) : ℝ) = ((↑((i - 1) / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
            int_sin_period ↑((i - 1) / 2 : ℕ) (by omega), mul_zero]
    ·
      unfold trigBasis
      simp only [show i ≠ 0 by omega, show i ≠ 1 by omega,
                 show j ≠ 0 by omega, show j ≠ 1 by omega, ite_false]

      by_cases hie : i % 2 = 0
      ·
        simp only [show (i % 2 = 0) = True from by simp [hie], ite_true]
        by_cases hje : j % 2 = 0
        ·
          simp only [show (j % 2 = 0) = True from by simp [hje], ite_true]
          have heq : (fun x : ℝ => √2 * cos (2 * π * ↑(i / 2) * x) * (√2 * cos (2 * π * ↑(j / 2) * x))) =
              (fun x => 2 * (cos (2 * π * ↑(i / 2) * x) * cos (2 * π * ↑(j / 2) * x))) := by
            ext x; rw [show √2 * cos (2 * π * ↑(i / 2) * x) * (√2 * cos (2 * π * ↑(j / 2) * x)) =
              (√2 * √2) * (cos (2 * π * ↑(i / 2) * x) * cos (2 * π * ↑(j / 2) * x)) from by ring, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
              int_cos_cos _ _ (by omega) (by omega)]
          split_ifs with hab hij
          · norm_num
          · exfalso; exact hij (by omega)
          · exfalso; exact hab (by omega)
          · norm_num
        ·
          simp only [show (j % 2 = 0) = False from by simp [hje], ite_false]
          have heq : (fun x : ℝ => √2 * cos (2 * π * ↑(i / 2) * x) * (√2 * sin (2 * π * ↑((j - 1) / 2) * x))) =
              (fun x => 2 * (cos (2 * π * ↑(i / 2) * x) * sin (2 * π * ↑((j - 1) / 2) * x))) := by
            ext x; rw [show √2 * cos _ * (√2 * sin _) = (√2 * √2) * (cos _ * sin _) from by ring, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
              int_cos_sin _ _ (by omega) (by omega), mul_zero,
              if_neg (show ¬(i = j) from by omega)]
      ·
        simp only [show (i % 2 = 0) = False from by simp [hie], ite_false]
        by_cases hje : j % 2 = 0
        ·
          simp only [show (j % 2 = 0) = True from by simp [hje], ite_true]
          have heq : (fun x : ℝ => √2 * sin (2 * π * ↑((i - 1) / 2) * x) * (√2 * cos (2 * π * ↑(j / 2) * x))) =
              (fun x => 2 * (sin (2 * π * ↑((i - 1) / 2) * x) * cos (2 * π * ↑(j / 2) * x))) := by
            ext x; rw [show √2 * sin _ * (√2 * cos _) = (√2 * √2) * (sin _ * cos _) from by ring, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
              int_sin_cos _ _ (by omega) (by omega), mul_zero,
              if_neg (show ¬(i = j) from by omega)]
        ·
          simp only [show (j % 2 = 0) = False from by simp [hje], ite_false]
          have heq : (fun x : ℝ => √2 * sin (2 * π * ↑((i - 1) / 2) * x) * (√2 * sin (2 * π * ↑((j - 1) / 2) * x))) =
              (fun x => 2 * (sin (2 * π * ↑((i - 1) / 2) * x) * sin (2 * π * ↑((j - 1) / 2) * x))) := by
            ext x
            have : √2 * sin (2 * π * ↑((i - 1) / 2) * x) * (√2 * sin (2 * π * ↑((j - 1) / 2) * x)) =
              (√2 * √2) * (sin (2 * π * ↑((i - 1) / 2) * x) * sin (2 * π * ↑((j - 1) / 2) * x)) := by ring
            rw [this, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
              int_sin_sin _ _ (by omega) (by omega)]
          split_ifs with hab hij
          · norm_num
          · exfalso; exact hij (by omega)
          · exfalso; exact hab (by omega)
          · norm_num

/-- Every trigonometric basis function `φ_j` is continuous on `ℝ`. -/
lemma trigBasis_continuous (j : ℕ) : Continuous (trigBasis j) := by
  unfold trigBasis; split_ifs <;> fun_prop

/-- Parseval-style identity for the truncated Fourier expansion: the `L²` error
of the `N`-term partial sum equals `‖g‖²₂` minus the sum of squared Fourier
coefficients. -/
theorem trigBasis_L2_error_eq (g : ℝ → ℝ)
    (hg : IntegrableOn (fun x => (g x) ^ 2) (Icc 0 1))
    (hg_int : IntegrableOn g (Icc 0 1)) (N : ℕ) :
    ∫ x in Icc (0 : ℝ) 1,
      (g x - ∑ k ∈ Finset.range N,
        (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
          trigBasis (k + 1) x) ^ 2 =
    (∫ x in Icc (0 : ℝ) 1, (g x) ^ 2) -
      ∑ k ∈ Finset.range N,
        (∫ x in Icc (0 : ℝ) 1, g x * trigBasis (k + 1) x) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>

    have hLHS_eq : (fun x => (g x - ∑ k ∈ Finset.range (N + 1),
        (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
          trigBasis (k + 1) x) ^ 2) =
        (fun x => ((g x - ∑ k ∈ Finset.range N,
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
              trigBasis (k + 1) x) -
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (N + 1) t) *
            trigBasis (N + 1) x) ^ 2) := by
      ext x; congr 1; rw [Finset.sum_range_succ]; ring
    rw [show ∫ x in Icc (0 : ℝ) 1,
        (g x - ∑ k ∈ Finset.range (N + 1),
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
            trigBasis (k + 1) x) ^ 2 =
        ∫ x in Icc (0 : ℝ) 1,
          ((g x - ∑ k ∈ Finset.range N,
              (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
                trigBasis (k + 1) x) -
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (N + 1) t) *
              trigBasis (N + 1) x) ^ 2 by
      congr 1]

    rw [Finset.sum_range_succ]

    set cN := ∫ t in Icc (0 : ℝ) 1, g t * trigBasis (N + 1) t
    set R := fun x => g x - ∑ k ∈ Finset.range N,
        (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
          trigBasis (k + 1) x


    have hφ_sq : ∫ x in Icc (0 : ℝ) 1, trigBasis (N + 1) x * trigBasis (N + 1) x = 1 := by
      have := trigBasis_orthonormal (N + 1) (N + 1) (by omega) (by omega)
      simp at this; exact this

    have hcross : ∫ x in Icc (0 : ℝ) 1, R x * trigBasis (N + 1) x = cN := by

      have hgφ_int : IntegrableOn (fun x => g x * trigBasis (N + 1) x) (Icc (0 : ℝ) 1) :=
        hg_int.mul_continuousOn (trigBasis_continuous (N + 1)).continuousOn isCompact_Icc
      have hS_cont : Continuous (fun x => ∑ k ∈ Finset.range N,
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) :=
        continuous_finset_sum _ (fun k _ => continuous_const.mul (trigBasis_continuous (k + 1)))
      have hSφ_int : IntegrableOn (fun x => (∑ k ∈ Finset.range N,
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) *
          trigBasis (N + 1) x) (Icc (0 : ℝ) 1) :=
        (hS_cont.mul (trigBasis_continuous (N + 1))).continuousOn.integrableOn_compact isCompact_Icc

      have hsplit : ∫ x in Icc (0 : ℝ) 1, R x * trigBasis (N + 1) x =
          (∫ x in Icc (0 : ℝ) 1, g x * trigBasis (N + 1) x) -
          ∫ x in Icc (0 : ℝ) 1, (∑ k ∈ Finset.range N,
              (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) *
              trigBasis (N + 1) x := by
        have : (fun x => R x * trigBasis (N + 1) x) =
            (fun x => g x * trigBasis (N + 1) x -
              (∑ k ∈ Finset.range N,
                (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) *
              trigBasis (N + 1) x) := by
          ext x; show (g x - _) * _ = _; ring
        rw [this, integral_sub hgφ_int hSφ_int]
      rw [hsplit]

      have hSφ_zero : ∫ x in Icc (0 : ℝ) 1, (∑ k ∈ Finset.range N,
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) *
          trigBasis (N + 1) x = 0 := by
        have step1 : ∀ x, (∑ k ∈ Finset.range N,
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) *
            trigBasis (N + 1) x =
          ∑ k ∈ Finset.range N,
            ((∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x *
              trigBasis (N + 1) x) := by
          intro x; rw [Finset.sum_mul]
        simp_rw [step1]
        rw [integral_finset_sum]
        · apply Finset.sum_eq_zero; intro k hk
          simp_rw [show ∀ a, (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
              trigBasis (k + 1) a * trigBasis (N + 1) a =
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) *
              (trigBasis (k + 1) a * trigBasis (N + 1) a) from fun a => by ring]
          rw [integral_const_mul,
              trigBasis_orthonormal (k + 1) (N + 1) (by omega) (by omega),
              if_neg (show k + 1 ≠ N + 1 from by
                simp [Finset.mem_range] at hk; omega)]
          ring
        · intro k _
          exact ((continuous_const.mul (trigBasis_continuous (k + 1))).mul
            (trigBasis_continuous (N + 1))).continuousOn.integrableOn_compact isCompact_Icc
      rw [hSφ_zero, sub_zero]

    have hexpand : ∫ x in Icc (0 : ℝ) 1, (R x - cN * trigBasis (N + 1) x) ^ 2 =
        (∫ x in Icc (0 : ℝ) 1, (R x) ^ 2) -
        2 * cN * (∫ x in Icc (0 : ℝ) 1, R x * trigBasis (N + 1) x) +
        cN ^ 2 * (∫ x in Icc (0 : ℝ) 1, trigBasis (N + 1) x * trigBasis (N + 1) x) := by

      have hR_int : IntegrableOn R (Icc (0 : ℝ) 1) := by
        apply IntegrableOn.sub hg_int
        exact (continuous_finset_sum _ (fun k _ =>
          continuous_const.mul (trigBasis_continuous (k + 1)))).continuousOn.integrableOn_compact
          isCompact_Icc
      have hS_cont : Continuous (fun x => ∑ k ∈ Finset.range N,
          (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) :=
        continuous_finset_sum _ (fun k _ => continuous_const.mul (trigBasis_continuous (k + 1)))
      have hRsq : IntegrableOn (fun x => (R x) ^ 2) (Icc (0 : ℝ) 1) := by
        have hgS : IntegrableOn (fun x => g x * (∑ k ∈ Finset.range N,
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x))
            (Icc (0 : ℝ) 1) :=
          hg_int.mul_continuousOn hS_cont.continuousOn isCompact_Icc
        have hSsq : IntegrableOn (fun x => (∑ k ∈ Finset.range N,
            (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) ^ 2)
            (Icc (0 : ℝ) 1) :=
          (hS_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
        have heq : (fun x => (R x) ^ 2) = (fun x => g x ^ 2 - 2 * (g x *
            (∑ k ∈ Finset.range N,
              (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x)) +
            (∑ k ∈ Finset.range N,
              (∫ t in Icc (0 : ℝ) 1, g t * trigBasis (k + 1) t) * trigBasis (k + 1) x) ^ 2) := by
          ext x; simp only [R]; ring
        rw [heq]
        exact (hg.sub (hgS.const_mul 2)).add hSsq
      have hRφ : IntegrableOn (fun x => R x * trigBasis (N + 1) x) (Icc (0 : ℝ) 1) :=
        hR_int.mul_continuousOn (trigBasis_continuous (N + 1)).continuousOn isCompact_Icc
      have hφsq : IntegrableOn (fun x => trigBasis (N + 1) x * trigBasis (N + 1) x)
          (Icc (0 : ℝ) 1) :=
        ((trigBasis_continuous (N + 1)).mul (trigBasis_continuous (N + 1))).continuousOn.integrableOn_compact
          isCompact_Icc

      have h_rw : (fun x => (R x - cN * trigBasis (N + 1) x) ^ 2) =
          (fun x => R x ^ 2 + (-(2 * cN) * (R x * trigBasis (N + 1) x) +
            cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x))) := by
        ext x; ring
      rw [h_rw]
      have h_cRφ : IntegrableOn (fun x => -(2 * cN) * (R x * trigBasis (N + 1) x))
          (Icc (0 : ℝ) 1) := hRφ.const_mul _
      have h_cφsq : IntegrableOn (fun x => cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x))
          (Icc (0 : ℝ) 1) := hφsq.const_mul _
      have step1 : ∫ x in Icc (0 : ℝ) 1,
          R x ^ 2 + (-(2 * cN) * (R x * trigBasis (N + 1) x) +
            cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x)) =
        (∫ x in Icc (0 : ℝ) 1, R x ^ 2) +
        ∫ x in Icc (0 : ℝ) 1, (-(2 * cN) * (R x * trigBasis (N + 1) x) +
            cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x)) :=
        integral_add hRsq (h_cRφ.add h_cφsq)
      have step2 : ∫ x in Icc (0 : ℝ) 1,
          (-(2 * cN) * (R x * trigBasis (N + 1) x) +
            cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x)) =
        (∫ x in Icc (0 : ℝ) 1, -(2 * cN) * (R x * trigBasis (N + 1) x)) +
        ∫ x in Icc (0 : ℝ) 1, cN ^ 2 * (trigBasis (N + 1) x * trigBasis (N + 1) x) :=
        integral_add h_cRφ h_cφsq
      rw [step1, step2, integral_const_mul, integral_const_mul]
      ring
    rw [hcross, hφ_sq] at hexpand
    nlinarith [ih, hexpand]






/-- Two summable sequences with equal first term and matching sums of consecutive
odd+even pairs have equal series sums. -/
lemma parity_regroup_sum' (f g : ℕ → ℝ)
    (h0 : f 0 = g 0)
    (hpair : ∀ k, f (2 * k + 1) + f (2 * (k + 1)) = g (2 * k + 1) + g (2 * (k + 1)))
    (hfs : Summable f) (hgs : Summable g) :
    ∑' k, f k = ∑' k, g k := by
  set h := fun k => f (k + 1) with hh_def
  set h' := fun k => g (k + 1) with hh'_def
  have hhs : Summable h := (summable_nat_add_iff 1).mpr hfs
  have hh's : Summable h' := (summable_nat_add_iff 1).mpr hgs
  rw [tsum_eq_zero_add' hhs, tsum_eq_zero_add' hh's, h0]
  congr 1
  have hhe : Summable (fun k => h (2 * k)) := hhs.comp_injective (fun a b h => by omega)
  have hho : Summable (fun k => h (2 * k + 1)) := hhs.comp_injective (fun a b h => by omega)
  have hh'e : Summable (fun k => h' (2 * k)) := hh's.comp_injective (fun a b h => by omega)
  have hh'o : Summable (fun k => h' (2 * k + 1)) := hh's.comp_injective (fun a b h => by omega)
  rw [← tsum_even_add_odd hhe hho, ← tsum_even_add_odd hh'e hh'o,
      ← hhe.tsum_add hho, ← hh'e.tsum_add hh'o]
  apply tsum_congr
  intro k
  simp only [hh_def, hh'_def]
  have key := hpair k
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega]
  exact key

/-- The companion map on `ℕ`: pairs `2k+1 ↔ 2k+2`, fixing `0`. Used to bound
a sequence by sums of paired terms. -/
def companion : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then n + 2 else n

/-- The companion map is injective. -/
lemma companion_injective : Function.Injective companion := by
  intro a b hab
  match a, b with
  | 0, 0 => rfl
  | 0, b + 1 => simp [companion] at hab; split_ifs at hab; all_goals omega
  | a + 1, 0 => simp [companion] at hab; split_ifs at hab; all_goals omega
  | a + 1, b + 1 =>
    simp only [companion] at hab
    split_ifs at hab <;> omega

/-- If a nonnegative sequence `f` is summable and a nonnegative sequence `g`
matches `f` on pairs `(2k+1, 2k+2)` and at `0`, then `g` is also summable. -/
lemma summable_of_pair_eq (f g : ℕ → ℝ) (hf_nn : ∀ k, 0 ≤ f k) (hg_nn : ∀ k, 0 ≤ g k)
    (hf_sum : Summable f)
    (h0 : f 0 = g 0)
    (hpair : ∀ k, f (2 * k + 1) + f (2 * (k + 1)) = g (2 * k + 1) + g (2 * (k + 1))) :
    Summable g := by
  have hbound : ∀ n, g n ≤ f n + f (companion n) := by
    intro n
    match n with
    | 0 =>
      simp only [companion]
      linarith [h0.symm, hf_nn 0]
    | n + 1 =>
      simp only [companion]
      by_cases hodd : (n + 1) % 2 = 1
      · simp only [hodd, if_true]
        have hk := hpair (n / 2)
        have h1 : 2 * (n / 2) + 1 = n + 1 := by omega
        have h2 : 2 * (n / 2 + 1) = n + 2 := by omega
        rw [h1, h2] at hk
        linarith [hg_nn (n + 2)]
      · simp only [hodd, if_false]
        have hk := hpair ((n + 1) / 2 - 1)
        have h1 : 2 * ((n + 1) / 2 - 1) + 1 = n := by omega
        have h2 : 2 * ((n + 1) / 2 - 1 + 1) = n + 1 := by omega
        rw [h1, h2] at hk
        linarith [hg_nn n]
  exact Summable.of_nonneg_of_le hg_nn (fun n => hbound n)
    (hf_sum.add (hf_sum.comp_injective companion_injective))








end Chapter3
