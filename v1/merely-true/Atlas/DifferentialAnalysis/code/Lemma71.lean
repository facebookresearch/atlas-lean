/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section

open scoped SchwartzMap
open SchwartzMap

namespace TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Melrose Lemma 7.1: equivalence between the two standard ways of characterising
Schwartz decay of a smooth function. The "polynomial weight" formulation
(bounded `‖x‖^k ‖∂^n f(x)‖` for all `k, n`) is equivalent to the "(1 + ‖x‖)-weight"
formulation, restricted to indices satisfying `n ≤ k`. -/
theorem schwartz_iff_weightedDeriv_bounded {f : E → F}
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    (∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) ↔
    (∀ k n : ℕ, n ≤ k → ∃ C : ℝ, ∀ x,
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) := by
  constructor
  ·

    intro hdecay k n _hn
    let g : 𝓢(E, F) := ⟨f, hsmooth, hdecay⟩
    exact ⟨2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g,
      fun x => SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl g x⟩
  ·


    intro hdecay j n
    obtain ⟨C, hC⟩ := hdecay (max j n) n (le_max_right j n)
    exact ⟨C, fun x => calc
      ‖x‖ ^ j * ‖iteratedFDeriv ℝ n f x‖
        ≤ (1 + ‖x‖) ^ j * ‖iteratedFDeriv ℝ n f x‖ := by
          gcongr; linarith [norm_nonneg x]
      _ ≤ (1 + ‖x‖) ^ max j n * ‖iteratedFDeriv ℝ n f x‖ := by
          gcongr
          · linarith [norm_nonneg x]
          · exact le_max_left j n
      _ ≤ C := hC x⟩

/-- For any Schwartz function `f`, each weighted derivative norm
`(1 + ‖x‖)^k ‖∂^n f(x)‖` admits an explicit nonnegative bound expressed via the
Schwartz seminorms of `f`. -/
theorem schwartz_weightedDeriv_bounded (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity, fun x => ?_⟩
  exact SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl f x

end TemperedDistributions

end
