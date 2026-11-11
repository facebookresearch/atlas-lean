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

theorem fourierCoeff_noiseOperator {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff (noiseOperator ρ f) S = ρ ^ S.card * fourierCoeff f S := by
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  unfold fourierCoeff
  simp_rw [noiseOperator_eq_fourier_sum]


  simp_rw [Finset.sum_mul]


  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


  simp_rw [show ∀ (T : Finset (Fin n)) (x : Fin n → Bool),
    1 / (2 : ℝ) ^ n * (ρ ^ T.card * fourierCoeff f T * chi T x * chi S x) =
    (ρ ^ T.card * fourierCoeff f T) * (1 / (2 : ℝ) ^ n * (chi T x * chi S x))
    from fun T x => by ring]
  simp_rw [← Finset.mul_sum]

  simp_rw [sum_chi_mul_chi_eq]

  simp_rw [mul_ite, mul_zero]
  simp only [one_div, inv_mul_cancel₀ h2n_ne]
  simp_rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simp only [fourierCoeff, mul_one]
  ring

theorem noiseOperator_comp {n : ℕ} (ρ σ : ℝ) (f : (Fin n → Bool) → ℝ) :
    noiseOperator ρ (noiseOperator σ f) = noiseOperator (ρ * σ) f := by
  funext x
  simp_rw [noiseOperator_eq_fourier_sum]
  congr 1
  ext S

  rw [fourierCoeff_noiseOperator σ f S, mul_pow]
  ring

end BooleanFourier
