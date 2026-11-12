/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Monotone
import Atlas.BooleanFunctions.code.NoiseSensitivity
import Atlas.BooleanFunctions.code.Talagrand
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.UniqueGames
import Atlas.BooleanFunctions.code.Theorems
import Atlas.BooleanFunctions.code.Lemma26Lec10

open Finset BigOperators

namespace BooleanFourier

noncomputable def pBiasedTotalInfluence {n : ℕ} (p : ℝ)
    (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ i : Fin n, (∑ x : Fin n → Bool,
    (∏ j : Fin n, if x j = true then p else (1 - p)) *
    if f x ≠ f (flipCoord x i) then (1 : ℝ) else 0)

noncomputable def criticalProb {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧
    (∑ x : Fin n → Bool,
      (∏ j : Fin n, if x j = true then p else (1 - p)) *
      if f x = true then (1 : ℝ) else 0) ≤ 1 / 2}

theorem monotone_fourierCoeff_singleton_nonneg {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : IsMonotone f) (i : Fin n) :
    0 ≤ fourierCoeff (fun x => boolToReal (f x)) {i} := by
  rw [monotone_fourierCoeff_singleton_eq_influence f hf i]
  simp only [influence]
  positivity

theorem spectral_sample_expected_cardinality {n : ℕ}
    (f : (Fin n → Bool) → ℝ) :
    ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f S ^ 2 =
    ∑ i : Fin n, fourierInfluence f i := by
  classical
  unfold fourierInfluence
  have key : ∀ S : Finset (Fin n),
      (S.card : ℝ) * fourierCoeff f S ^ 2 =
      ∑ i : Fin n, if i ∈ S then fourierCoeff f S ^ 2 else 0 := by
    intro S
    have h1 : (S.card : ℝ) = ∑ i : Fin n,
        if i ∈ S then (1 : ℝ) else 0 := by
      trans ((Finset.univ.filter (fun i : Fin n => i ∈ S)).card : ℝ)
      · congr 1
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      · rw [← Finset.sum_boole]
    rw [h1, Finset.sum_mul]
    congr 1
    ext i
    split_ifs <;> ring
  simp_rw [key]
  rw [Finset.sum_comm]

end BooleanFourier

theorem BooleanFourier.noiseSensitivity_dictator {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    BooleanFourier.noiseSensitivity δ (fun x : Fin n → Bool => x ⟨0, hn⟩) = δ := by
  unfold BooleanFourier.noiseSensitivity

  have hfun : (fun x : Fin n → Bool => BooleanFourier.boolToReal (x ⟨0, hn⟩)) =
      BooleanFourier.chi ({⟨0, hn⟩} : Finset (Fin n)) := by
    funext x
    exact (BooleanFourier.chi_singleton ⟨0, hn⟩ x).symm
  rw [hfun, BooleanFourier.noiseStability_chi_singleton]
  ring

theorem BooleanFourier.noiseSensitivity_le_totalInfluence_mul_delta {n : ℕ}
    (f : (Fin n → Bool) → Bool) (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    BooleanFourier.noiseSensitivity δ f ≤ δ * BooleanFourier.totalInfluence f := by

  rw [BooleanFourier.noiseSensitivity_eq_fourier_sum]

  rw [totalInfluence_eq_weighted_fourier']


  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _

  have hcoeff_sq : (0 : ℝ) ≤ BooleanFourier.fourierCoeff
      (fun x => BooleanFourier.boolToReal (f x)) S ^ 2 := sq_nonneg _

  suffices h : 1 / 2 * (1 - (1 - 2 * δ) ^ S.card) ≤ δ * ↑S.card by
    have h1 : 1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) *
        BooleanFourier.fourierCoeff (fun x => BooleanFourier.boolToReal (f x)) S ^ 2) =
      (1 / 2 * (1 - (1 - 2 * δ) ^ S.card)) *
        BooleanFourier.fourierCoeff (fun x => BooleanFourier.boolToReal (f x)) S ^ 2 := by
      ring
    have h2 : δ * (↑S.card * BooleanFourier.fourierCoeff
        (fun x => BooleanFourier.boolToReal (f x)) S ^ 2) =
      (δ * ↑S.card) *
        BooleanFourier.fourierCoeff (fun x => BooleanFourier.boolToReal (f x)) S ^ 2 := by
      ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right h hcoeff_sq


  have hρ : 0 ≤ 1 - 2 * δ := by linarith

  suffices bernoulli : ∀ k : ℕ, 1 - ↑k * (2 * δ) ≤ (1 - 2 * δ) ^ k by
    have key : 1 - (1 - 2 * δ) ^ S.card ≤ ↑S.card * (2 * δ) := by linarith [bernoulli S.card]
    linarith
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have : (1 - 2 * δ) ^ (m + 1) ≥ 1 - (↑m + 1) * (2 * δ) := by
      calc (1 - 2 * δ) ^ (m + 1)
          = (1 - 2 * δ) ^ m * (1 - 2 * δ) := pow_succ _ _
        _ ≥ (1 - ↑m * (2 * δ)) * (1 - 2 * δ) := by
            apply mul_le_mul_of_nonneg_right ih hρ
        _ = 1 - (↑m + 1) * (2 * δ) + ↑m * (2 * δ) ^ 2 := by ring
        _ ≥ 1 - (↑m + 1) * (2 * δ) := by
            linarith [mul_nonneg (Nat.cast_nonneg' m) (sq_nonneg (2 * δ))]
    push_cast at this ⊢
    linarith




