/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace CentralLimitTheorem

open Complex Finset

noncomputable def expTaylorRemainder (x : ℝ) : ℂ :=
  cexp (↑x * I) - 1 - ↑x * I - (↑x * I) ^ 2 / 2

lemma norm_ofReal_mul_I (x : ℝ) : ‖(↑x * I : ℂ)‖ = |x| := by
  rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]

lemma expTaylorRemainder_le_cube {x : ℝ} (hx : |x| ≤ 1) :
    ‖expTaylorRemainder x‖ ≤ |x| ^ 3 := by
  have key : expTaylorRemainder x =
      cexp (↑x * I) - ∑ m ∈ range 3, (↑x * I) ^ m / (m.factorial : ℂ) := by
    unfold expTaylorRemainder
    simp [sum_range_succ, Nat.factorial]
    ring
  rw [key]
  have hix : ‖(↑x * I : ℂ)‖ ≤ 1 := by rw [norm_ofReal_mul_I]; exact hx
  have h := exp_bound hix (n := 3) (by norm_num)
  rw [norm_ofReal_mul_I] at h
  calc ‖cexp (↑x * I) - ∑ m ∈ range 3, (↑x * I) ^ m / ↑m.factorial‖
      ≤ |x| ^ 3 * ((4 : ℝ) * ((6 : ℝ) * 3)⁻¹) := h
    _ ≤ |x| ^ 3 * 1 := by gcongr; norm_num
    _ = |x| ^ 3 := mul_one _

lemma expTaylorRemainder_le_sq {x : ℝ} (hx : 1 ≤ |x|) :
    ‖expTaylorRemainder x‖ ≤ 4 * |x| ^ 2 := by
  unfold expTaylorRemainder
  have hexp : ‖cexp (↑x * I)‖ = 1 := norm_exp_ofReal_mul_I x
  calc ‖cexp (↑x * I) - 1 - ↑x * I - (↑x * I) ^ 2 / 2‖
      ≤ ‖cexp (↑x * I)‖ + ‖(1 : ℂ)‖ + ‖(↑x * I : ℂ)‖ + ‖((↑x * I) ^ 2 / 2 : ℂ)‖ := by
        calc _ ≤ ‖cexp (↑x * I) - 1 - ↑x * I‖ + ‖(↑x * I) ^ 2 / 2‖ := norm_sub_le _ _
          _ ≤ (‖cexp (↑x * I) - 1‖ + ‖↑x * I‖) + ‖(↑x * I) ^ 2 / 2‖ := by
              gcongr; exact norm_sub_le _ _
          _ ≤ (‖cexp (↑x * I)‖ + ‖(1 : ℂ)‖ + ‖↑x * I‖) + ‖(↑x * I) ^ 2 / 2‖ := by
              gcongr; exact norm_sub_le _ _
          _ = _ := by ring
    _ = 2 + |x| + |x| ^ 2 / 2 := by
        rw [hexp, norm_one, norm_ofReal_mul_I, norm_div, norm_pow, norm_ofReal_mul_I, norm_ofNat]
        ring
    _ ≤ 4 * |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]

theorem expTaylorRemainder_le_min (x : ℝ) :
    ‖expTaylorRemainder x‖ ≤ 4 * min (|x| ^ 2) (|x| ^ 3) := by
  by_cases hx : |x| ≤ 1
  ·
    have hmin : min (|x| ^ 2) (|x| ^ 3) = |x| ^ 3 := by
      rw [min_eq_right]
      calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
        _ ≤ |x| ^ 2 * 1 := by gcongr
        _ = |x| ^ 2 := mul_one _
    rw [hmin]
    calc ‖expTaylorRemainder x‖ ≤ |x| ^ 3 := expTaylorRemainder_le_cube hx
      _ ≤ 1 * |x| ^ 3 := (one_mul _).symm.le
      _ ≤ 4 * |x| ^ 3 := by gcongr; norm_num
  ·
    have hx' : 1 ≤ |x| := (not_le.mp hx).le
    have hmin : min (|x| ^ 2) (|x| ^ 3) = |x| ^ 2 := by
      rw [min_eq_left]
      calc |x| ^ 2 = |x| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |x| ^ 2 * |x| := by gcongr
        _ = |x| ^ 3 := by ring
    rw [hmin]
    exact expTaylorRemainder_le_sq hx'

theorem min_pow_le_rpow (x : ℝ) (α : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ (2 + α) := by
  by_cases hx : |x| ≤ 1
  · calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 3 := min_le_right _ _
      _ = |x| ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast |x| 3).symm
      _ ≤ |x| ^ (2 + α) := by
          apply Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg x) hx (by linarith)
          push_cast; linarith
  · have hx' : 1 ≤ |x| := (not_le.mp hx).le
    calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 2 := min_le_left _ _
      _ = |x| ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast |x| 2).symm
      _ ≤ |x| ^ (2 + α) := by
          apply Real.rpow_le_rpow_of_exponent_le hx'
          push_cast; linarith

theorem expTaylorRemainder_le_rpow (x : ℝ) (α : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    ‖expTaylorRemainder x‖ ≤ 4 * |x| ^ (2 + α) := by
  calc ‖expTaylorRemainder x‖
      ≤ 4 * min (|x| ^ 2) (|x| ^ 3) := expTaylorRemainder_le_min x
    _ ≤ 4 * |x| ^ (2 + α) := by
        gcongr
        exact min_pow_le_rpow x α hα1 hα2

section CLT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

lemma memLp_two_of_higher_moment {X : Ω → ℝ} {α : ℝ} (hα : 0 < α)
    (hLp : MemLp X (ENNReal.ofReal (2 + α)) P) :
    MemLp X 2 P := by
  apply hLp.mono_exponent
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem central_limit_theorem
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} {α : ℝ}
    (hα : 0 < α)
    (hLp : MemLp (X 0) (ENNReal.ofReal (2 + α)) P)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√↑n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - ↑n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub hY
    (memLp_two_of_higher_moment hα hLp) hindep hident

end CLT

end CentralLimitTheorem
