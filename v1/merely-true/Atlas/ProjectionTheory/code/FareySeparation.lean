/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace FareySeparation

/--
Farey separation lemma: if `a₁/p₁` and `a₂/p₂` are distinct rationals with prime
denominators `p₁, p₂ ≤ M`, then
$$\left|\frac{a_1}{p_1} - \frac{a_2}{p_2}\right| \;\ge\; \frac{1}{M^2}.$$
Proven by clearing denominators: `|a₁ p₂ - a₂ p₁| ≥ 1` is an integer, and
`p₁ p₂ ≤ M²`. This is the key separation property used in the proof of Linnik's
large sieve inequality.
-/
theorem farey_separation
    (a₁ a₂ : ℤ) (p₁ p₂ M : ℕ)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hp₁M : p₁ ≤ M) (hp₂M : p₂ ≤ M)
    (hne : (a₁ : ℚ) / p₁ ≠ (a₂ : ℚ) / p₂) :
    (1 : ℝ) / (M : ℝ) ^ 2 ≤ |((a₁ : ℝ) / (p₁ : ℝ)) - ((a₂ : ℝ) / (p₂ : ℝ))| := by
  have hp₁pos : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hp₁.pos
  have hp₂pos : (0 : ℝ) < (p₂ : ℝ) := by exact_mod_cast hp₂.pos
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le hp₁.pos hp₁M
  have hp₁ne : (p₁ : ℝ) ≠ 0 := ne_of_gt hp₁pos
  have hp₂ne : (p₂ : ℝ) ≠ 0 := ne_of_gt hp₂pos

  have hne_int : a₁ * (p₂ : ℤ) ≠ a₂ * (p₁ : ℤ) := by
    intro heq
    apply hne
    rw [div_eq_div_iff (by exact_mod_cast hp₁.ne_zero : (p₁ : ℚ) ≠ 0)
        (by exact_mod_cast hp₂.ne_zero : (p₂ : ℚ) ≠ 0)]
    exact_mod_cast heq

  have hnum_int : (1 : ℤ) ≤ |a₁ * (p₂ : ℤ) - a₂ * (p₁ : ℤ)| :=
    Int.one_le_abs (sub_ne_zero.mpr hne_int)

  have hdenom : (p₁ : ℝ) * (p₂ : ℝ) ≤ (M : ℝ) ^ 2 := by
    calc (p₁ : ℝ) * (p₂ : ℝ) ≤ (M : ℝ) * (M : ℝ) := by
          apply mul_le_mul <;> [exact_mod_cast hp₁M; exact_mod_cast hp₂M;
            exact le_of_lt hp₂pos; linarith]
      _ = (M : ℝ) ^ 2 := (sq (M : ℝ)).symm

  suffices h : (1 : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)) ≤
      |((a₁ : ℝ) / (p₁ : ℝ)) - ((a₂ : ℝ) / (p₂ : ℝ))| by
    calc (1 : ℝ) / (M : ℝ) ^ 2
        ≤ 1 / ((p₁ : ℝ) * (p₂ : ℝ)) := by
          apply div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ 1)
            (mul_pos hp₁pos hp₂pos) hdenom
      _ ≤ _ := h

  rw [div_sub_div _ _ hp₁ne hp₂ne, abs_div, abs_of_pos (mul_pos hp₁pos hp₂pos)]
  apply div_le_div_of_nonneg_right _ (by positivity)

  have h : ((a₁ : ℝ) * (↑p₂ : ℝ) - (↑p₁ : ℝ) * (↑a₂ : ℝ)) =
    ((a₁ * (p₂ : ℤ) - a₂ * (p₁ : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h, ← Int.cast_abs]
  exact_mod_cast hnum_int

end FareySeparation
