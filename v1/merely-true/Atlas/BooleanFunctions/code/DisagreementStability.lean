/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseSensitivity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset BigOperators

namespace BooleanFourier

noncomputable def disagreementProb {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (1 - f x * noiseOperator ρ f x) / 2

theorem disagreementProb_eq {n : ℕ} (ρ : ℝ)
    (f : (Fin n → Bool) → ℝ) :
    disagreementProb ρ f = (1 - noiseStability ρ f) / 2 := by
  simp only [disagreementProb, noiseStability]
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos

  have hfactor : ∀ x : Fin n → Bool,
      (1 - f x * noiseOperator ρ f x) / 2 =
      (1 : ℝ) / 2 - (1 : ℝ) / 2 * (f x * noiseOperator ρ f x) := fun x => by ring
  simp_rw [hfactor]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  push_cast
  field_simp

noncomputable def noiseSensitivityReal {n : ℕ} (δ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  disagreementProb (1 - 2 * δ) f

theorem noiseSensitivityReal_eq {n : ℕ} (δ : ℝ)
    (f : (Fin n → Bool) → ℝ) :
    noiseSensitivityReal δ f = (1 - noiseStability (1 - 2 * δ) f) / 2 := by
  exact disagreementProb_eq (1 - 2 * δ) f

theorem noiseSensitivity_eq {n : ℕ} (δ : ℝ)
    (f : (Fin n → Bool) → Bool) :
    noiseSensitivity δ f =
      (1 - noiseStability (1 - 2 * δ) (fun x => boolToReal (f x))) / 2 := by
  rfl

end BooleanFourier
