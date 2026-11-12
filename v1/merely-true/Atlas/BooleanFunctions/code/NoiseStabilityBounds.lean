/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseStability
import Atlas.BooleanFunctions.code.Theorems

set_option maxHeartbeats 800000

open Finset BigOperators

namespace BooleanFourier

theorem noiseStability_ge_fourierCoeff_empty_sq {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (f : (Fin n → Bool) → ℝ) :
    noiseStability ρ f ≥ fourierCoeff f ∅ ^ 2 := by
  rw [noiseStability_eq_sum]
  have hterm : ∀ S : Finset (Fin n),
      0 ≤ ρ ^ S.card * fourierCoeff f S ^ 2 :=
    fun S => mul_nonneg (pow_nonneg hρ₀ _) (sq_nonneg _)
  calc ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2
      ≥ ρ ^ (∅ : Finset (Fin n)).card * fourierCoeff f ∅ ^ 2 :=
        Finset.single_le_sum (fun S _ => hterm S) (Finset.mem_univ ∅)
    _ = fourierCoeff f ∅ ^ 2 := by simp

theorem noiseStability_le_sum_sq {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → ℝ) :
    noiseStability ρ f ≤ ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
  rw [noiseStability_eq_sum]
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ₀ hρ₁)

theorem noiseStability_bounds {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → ℝ) :
    fourierCoeff f ∅ ^ 2 ≤ noiseStability ρ f ∧
    noiseStability ρ f ≤ ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 :=
  ⟨noiseStability_ge_fourierCoeff_empty_sq ρ hρ₀ f,
   noiseStability_le_sum_sq ρ hρ₀ hρ₁ f⟩

theorem noiseStability_le_one_of_boolean {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → Bool) :
    noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 := by
  have h := noiseStability_le_sum_sq ρ hρ₀ hρ₁ (fun x => boolToReal (f x))
  linarith [parseval_signed f]

theorem noiseStability_bounds_boolean {n : ℕ} (ρ : ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (f : (Fin n → Bool) → Bool) :
    fourierCoeff (fun x => boolToReal (f x)) ∅ ^ 2
      ≤ noiseStability ρ (fun x => boolToReal (f x)) ∧
    noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 :=
  ⟨noiseStability_ge_fourierCoeff_empty_sq ρ hρ₀ _,
   noiseStability_le_one_of_boolean ρ hρ₀ hρ₁ f⟩

end BooleanFourier
