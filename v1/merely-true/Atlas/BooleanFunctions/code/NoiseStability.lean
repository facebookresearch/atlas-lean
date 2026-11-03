/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Stability

set_option maxHeartbeats 800000

open Finset BigOperators

namespace BooleanFourier

theorem noiseStability_eq_fourier_sum {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    noiseStability ρ f = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2 :=
  noiseStability_eq_sum ρ f

theorem noiseStability_one {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    noiseStability 1 f = ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
  rw [noiseStability_eq_sum]
  congr 1; ext S
  simp [one_pow]

theorem noiseStability_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    noiseStability 0 f = fourierCoeff f ∅ ^ 2 := by
  rw [noiseStability_eq_sum]
  classical
  have key : ∀ S : Finset (Fin n),
      (0 : ℝ) ^ S.card * fourierCoeff f S ^ 2 =
      if S = ∅ then fourierCoeff f S ^ 2 else 0 := by
    intro S
    split_ifs with h
    · subst h; simp
    · have hcard : S.card ≠ 0 := Finset.card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
      simp [zero_pow hcard]
  simp_rw [key]
  simp [Finset.sum_ite_eq']

theorem fourierCoeff_noiseOperator {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff (noiseOperator ρ f) S = ρ ^ S.card * fourierCoeff f S := by
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos

  show (1 / (2 : ℝ) ^ n) * ∑ x, noiseOperator ρ f x * chi S x =
    ρ ^ S.card * fourierCoeff f S

  simp_rw [noiseOperator_eq_fourier_sum]

  simp_rw [Finset.sum_mul]

  simp_rw [Finset.mul_sum]

  rw [Finset.sum_comm]

  simp_rw [show ∀ (T : Finset (Fin n)) (x : Fin n → Bool),
    1 / (2 : ℝ) ^ n * (ρ ^ T.card * fourierCoeff f T * chi T x * chi S x) =
    (1 / (2 : ℝ) ^ n) * (ρ ^ T.card * fourierCoeff f T) * (chi T x * chi S x)
    from fun T x => by ring]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_chi_mul_chi_eq]
  simp_rw [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  field_simp

end BooleanFourier
