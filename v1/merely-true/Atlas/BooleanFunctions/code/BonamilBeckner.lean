/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Hypercontractivity
import Atlas.BooleanFunctions.code.TwoPointInequality

open Finset BigOperators Real

namespace BooleanFourier

theorem noiseOp_snoc_eq_twoPointNoiseOp {m : ℕ} (ρ : ℝ) (f : BoolFn (m + 1))
    (x' : Fin m → Bool) (b : Bool) :
    noiseOp ρ f (Fin.snoc x' b) =
    twoPointNoiseOp ρ (fun c => noiseOp ρ (restrictLast f c) x') b := by
  simp only [noiseOp, twoPointNoiseOp, restrictLast]
  rw [sum_finBool_succ_split]
  simp_rw [Fin.prod_univ_castSucc]
  simp_rw [Fin.snoc_castSucc, Fin.snoc_last]

  cases b <;> simp only [boolToReal_true, boolToReal_false, ite_true, ite_false, Bool.false_eq_true]
  all_goals (simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; funext y'; ring)

set_option maxHeartbeats 800000 in

lemma lpNorm_convex_combination {m : ℕ} (g₁ g₂ : BoolFn m) (α β : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) {q : ℝ} (hq : 1 ≤ q) :
    lpNorm q (fun x => α * g₁ x + β * g₂ x) ≤ α * lpNorm q g₁ + β * lpNorm q g₂ := by
  unfold lpNorm
  have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h1q_nn : (0 : ℝ) ≤ 1 / q := by positivity

  have habs_bound : ∀ x : Fin m → Bool,
      |α * g₁ x + β * g₂ x| ^ q ≤ (α * |g₁ x| + β * |g₂ x|) ^ q := by
    intro x
    apply Real.rpow_le_rpow (abs_nonneg _) _ hq_pos.le
    calc |α * g₁ x + β * g₂ x|
        ≤ |α * g₁ x| + |β * g₂ x| := abs_add_le _ _
      _ = α * |g₁ x| + β * |g₂ x| := by
          rw [abs_mul, abs_of_nonneg hα, abs_mul, abs_of_nonneg hβ]
  have hsum_bound : (∑ x : Fin m → Bool, |α * g₁ x + β * g₂ x| ^ q) ≤
      (∑ x : Fin m → Bool, (α * |g₁ x| + β * |g₂ x|) ^ q) :=
    Finset.sum_le_sum (fun x _ => habs_bound x)

  have hMinkowski := Real.Lp_add_le_of_nonneg Finset.univ hq
    (fun i _ => mul_nonneg hα (abs_nonneg (g₁ i)))
    (fun i _ => mul_nonneg hβ (abs_nonneg (g₂ i)))

  have hpull_alpha : ∑ i : Fin m → Bool, (α * |g₁ i|) ^ q =
      α ^ q * ∑ i : Fin m → Bool, |g₁ i| ^ q := by
    simp_rw [Real.mul_rpow hα (abs_nonneg _)]; rw [Finset.mul_sum]
  have hpull_beta : ∑ i : Fin m → Bool, (β * |g₂ i|) ^ q =
      β ^ q * ∑ i : Fin m → Bool, |g₂ i| ^ q := by
    simp_rw [Real.mul_rpow hβ (abs_nonneg _)]; rw [Finset.mul_sum]
  rw [hpull_alpha, hpull_beta] at hMinkowski

  have hsimp_alpha : (α ^ q * ∑ i : Fin m → Bool, |g₁ i| ^ q) ^ (1 / q) =
      α * (∑ i : Fin m → Bool, |g₁ i| ^ q) ^ (1 / q) := by
    rw [Real.mul_rpow (rpow_nonneg hα q)
      (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    congr 1
    rw [← rpow_mul hα, mul_one_div_cancel (ne_of_gt hq_pos), rpow_one]
  have hsimp_beta : (β ^ q * ∑ i : Fin m → Bool, |g₂ i| ^ q) ^ (1 / q) =
      β * (∑ i : Fin m → Bool, |g₂ i| ^ q) ^ (1 / q) := by
    rw [Real.mul_rpow (rpow_nonneg hβ q)
      (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    congr 1
    rw [← rpow_mul hβ, mul_one_div_cancel (ne_of_gt hq_pos), rpow_one]
  rw [hsimp_alpha, hsimp_beta] at hMinkowski

  have h2m_factor : ∀ (S : ℝ), 0 ≤ S →
      (1 / (2 ^ m : ℝ) * S) ^ (1 / q) = (1 / (2 ^ m : ℝ)) ^ (1 / q) * S ^ (1 / q) :=
    fun S hS => Real.mul_rpow (by positivity) hS
  rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
  rw [show α * ((1 / (2 ^ m : ℝ)) * ∑ x, |g₁ x| ^ q) ^ (1 / q) +
      β * ((1 / (2 ^ m : ℝ)) * ∑ x, |g₂ x| ^ q) ^ (1 / q) =
      (1 / (2 ^ m : ℝ)) ^ (1 / q) *
        (α * (∑ x, |g₁ x| ^ q) ^ (1 / q) + β * (∑ x, |g₂ x| ^ q) ^ (1 / q)) from by
    rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_trans (rpow_le_rpow (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))
    hsum_bound h1q_nn) hMinkowski




end BooleanFourier
