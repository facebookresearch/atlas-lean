/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Atlas.DifferentialAnalysis.code.SchwartzSeminorms

open scoped SchwartzMap

noncomputable section

namespace TemperedDistributions

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative continuity of translation on Schwartz space: the `(k, n)`-th Schwartz
seminorm of the translated Schwartz function `φ(· − x)` is bounded by
`(1 + ‖x‖)^k · 2^k` times the supremum of the seminorms with indices in `Iic (k, n)`. -/
theorem SchwartzMap.seminorm_compSubConst_le
    (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [SMulCommClass ℝ 𝕜 ℂ]
    (k n : ℕ) (φ : 𝓢(E, ℂ)) (x : E) :
    SchwartzMap.seminorm 𝕜 k n (SchwartzMap.compSubConstCLM 𝕜 x φ) ≤
      (1 + ‖x‖) ^ k * 2 ^ k *
        (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) φ := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n
  · positivity
  intro y


  have hcoerce : ⇑(SchwartzMap.compSubConstCLM 𝕜 x φ) = fun z => φ (z - x) := by
    ext z; simp [SchwartzMap.compSubConstCLM_apply]
  rw [hcoerce, iteratedFDeriv_comp_sub]

  set z := y - x with hz_def

  have hy_le : ‖y‖ ≤ (1 + ‖z‖) * (1 + ‖x‖) := by
    calc ‖y‖ = ‖z + x‖ := by rw [hz_def, sub_add_cancel]
    _ ≤ ‖z‖ + ‖x‖ := norm_add_le z x
    _ ≤ (1 + ‖z‖) * (1 + ‖x‖) := by nlinarith [norm_nonneg z, norm_nonneg x]


  have hsup : (1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ n (⇑φ) z‖ ≤
      2 ^ k * (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) φ :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (k, n)) le_rfl le_rfl φ z

  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑φ) z‖
      ≤ ((1 + ‖z‖) * (1 + ‖x‖)) ^ k * ‖iteratedFDeriv ℝ n (⇑φ) z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hy_le k) (norm_nonneg _)
    _ = (1 + ‖x‖) ^ k * ((1 + ‖z‖) ^ k * ‖iteratedFDeriv ℝ n (⇑φ) z‖) := by
        rw [mul_pow]; ring
    _ ≤ (1 + ‖x‖) ^ k * (2 ^ k *
        (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) φ) :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = (1 + ‖x‖) ^ k * 2 ^ k *
        (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) φ := by ring

end TemperedDistributions

end
