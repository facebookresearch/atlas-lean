/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseSensitivity
import Atlas.BooleanFunctions.code.InfluenceFourier

open Finset BigOperators

namespace BooleanFourier

lemma one_sub_pow_le_mul_card (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (k : ℕ) :
    1 - (1 - t) ^ k ≤ t * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1t : 0 ≤ 1 - t := by linarith
    have h1t' : 1 - t ≤ 1 := by linarith
    calc 1 - (1 - t) ^ (k + 1)
        = 1 - (1 - t) ^ k * (1 - t) := by ring_nf
      _ = (1 - (1 - t) ^ k) + (1 - t) ^ k * t := by ring
      _ ≤ t * k + (1 - t) ^ k * t := by linarith
      _ ≤ t * k + 1 * t := by
          have : (1 - t) ^ k ≤ 1 := pow_le_one₀ h1t h1t'
          nlinarith
      _ = t * (k + 1) := by ring
      _ = t * ↑(k + 1) := by push_cast; ring

theorem noiseSensitivity_le_delta_mul_totalInfluenceReal {n : ℕ} (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 2) (f : (Fin n → Bool) → ℝ) :
    (1 / 2 * ∑ S : Finset (Fin n),
      (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) ≤
    δ * totalInfluenceReal f := by

  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]

  have h2δ_bound : 2 * δ ≤ 1 := by linarith
  have h2δ_nonneg : 0 ≤ 2 * δ := by linarith

  suffices h : ∀ S : Finset (Fin n),
      1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) ≤
      δ * ((S.card : ℝ) * fourierCoeff f S ^ 2) by
    calc 1 / 2 * ∑ S : Finset (Fin n),
          (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2
        = ∑ S : Finset (Fin n),
          1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ S : Finset (Fin n),
          δ * ((S.card : ℝ) * fourierCoeff f S ^ 2) :=
          Finset.sum_le_sum (fun S _ => h S)
      _ = δ * ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f S ^ 2 := by
          rw [← Finset.mul_sum]

  intro S
  have hfc_sq : 0 ≤ fourierCoeff f S ^ 2 := sq_nonneg _
  have hbern : 1 - (1 - 2 * δ) ^ S.card ≤ 2 * δ * S.card :=
    one_sub_pow_le_mul_card (2 * δ) h2δ_nonneg h2δ_bound S.card
  calc 1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2)
      ≤ 1 / 2 * (2 * δ * ↑S.card * fourierCoeff f S ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        exact mul_le_mul_of_nonneg_right hbern hfc_sq
    _ = δ * (↑S.card * fourierCoeff f S ^ 2) := by ring

theorem noiseSensitivity_le_delta_mul_totalInfluence {n : ℕ} (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 2) (f : (Fin n → Bool) → Bool) :
    noiseSensitivity δ f ≤ δ * totalInfluenceReal (fun x => boolToReal (f x)) := by

  rw [noiseSensitivity_eq_fourier_sum]

  exact noiseSensitivity_le_delta_mul_totalInfluenceReal δ hδ₀ hδ₁ _

end BooleanFourier
