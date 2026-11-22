/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseStabilityBounds

set_option maxHeartbeats 800000

open Finset BigOperators

namespace BooleanFourier

theorem noiseStability_mono {n : ℕ} (ρ σ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρσ : ρ ≤ σ) (f : (Fin n → Bool) → ℝ) :
    noiseStability ρ f ≤ noiseStability σ f := by
  rw [noiseStability_eq_sum, noiseStability_eq_sum]
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ hρ₀ hρσ S.card
  · exact sq_nonneg _

theorem noiseStability_at_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    noiseStability 0 f = fourierCoeff f ∅ ^ 2 :=
  noiseStability_zero f

theorem noiseStability_at_one_of_boolean {n : ℕ} (f : (Fin n → Bool) → Bool) :
    noiseStability 1 (fun x => boolToReal (f x)) = 1 := by
  rw [noiseStability_one]
  exact parseval_signed f

theorem noiseStability_bounds_of_boolean {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → Bool) :
    fourierCoeff (fun x => boolToReal (f x)) ∅ ^ 2
      ≤ noiseStability ρ (fun x => boolToReal (f x)) ∧
    noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 :=
  noiseStability_bounds_boolean ρ hρ₀ hρ₁ f

end BooleanFourier
