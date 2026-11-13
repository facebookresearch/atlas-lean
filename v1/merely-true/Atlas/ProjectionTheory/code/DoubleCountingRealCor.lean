/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.DoubleCountingReal
import Atlas.ProjectionTheory.code.HausdorffSpacing

open Finset BigOperators

namespace ProjectionTheory

/-- A `DoubleCountingRealSetup` augmented with the Hausdorff (a.k.a. dimension)
spacing hypotheses on both `X` and `D`: the covering numbers obey
`N_X(R^β) ≲ |X|^β` and `N_D(R^{β-1}) ≲ |D|^β` for every `β ∈ [0, 1]`. -/
structure DoubleCountingRealHausdorffSetup extends DoubleCountingRealSetup where
  C_X : ℝ
  hC_X_pos : 0 < C_X
  hHausdorff_X : ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    (N_X (R ^ β) : ℝ) ≤ C_X * (cardX : ℝ) ^ β
  C_D : ℝ
  hC_D_pos : 0 < C_D
  hHausdorff_D : ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
    (N_D (R ^ (β - 1)) : ℝ) ≤ C_D * (cardD : ℝ) ^ β

/-- **Corollary (Double Counting Real Version — dichotomy step).** Starting from the
intermediate bound `|D| ≲ log R · (S + S|D|/|X|)` produced by the real double-counting
theorem combined with Hausdorff spacing, conclude the dichotomy
`S ≳ |X|/log R   or   |D| ≲ log R · S`. -/
theorem double_counting_real_hausdorff_dichotomy_line683
    (setup : DoubleCountingRealHausdorffSetup)
    (hX_pos : 0 < setup.cardX)
    (hD_pos : 0 < setup.cardD)
    (hR_gt : 1 < setup.R)
    (h_intermediate : ∃ C : ℝ, C > 0 ∧ (setup.cardD : ℝ) ≤ C * Real.log setup.R *
      ((setup.S : ℝ) + (setup.S : ℝ) * (setup.cardD : ℝ) / (setup.cardX : ℝ))) :
    ∃ C : ℝ, C > 0 ∧
      ((setup.S : ℝ) ≥ (setup.cardX : ℝ) / (C * Real.log setup.R) ∨
       (setup.cardD : ℝ) ≤ C * Real.log setup.R * (setup.S : ℝ)) := by
  obtain ⟨C, hC_pos, hbound⟩ := h_intermediate
  have hlogR_pos : (0 : ℝ) < Real.log setup.R := Real.log_pos hR_gt
  have hX_pos' : (0 : ℝ) < (setup.cardX : ℝ) := Nat.cast_pos.mpr hX_pos
  have hD_nn : (0 : ℝ) ≤ (setup.cardD : ℝ) := Nat.cast_nonneg' _
  refine ⟨2 * C, by linarith, ?_⟩
  by_cases h : C * Real.log setup.R * (setup.S : ℝ) / (setup.cardX : ℝ) ≥ 1 / 2
  ·
    left
    rw [ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C * Real.log setup.R)]
    have h' : 1 / 2 * (setup.cardX : ℝ) ≤ C * Real.log setup.R * (setup.S : ℝ) := by
      rwa [ge_iff_le, le_div_iff₀ hX_pos'] at h
    nlinarith
  ·
    right
    simp only [ge_iff_le, not_le] at h
    have key : (setup.cardD : ℝ) * (setup.cardX : ℝ) ≤
        C * Real.log setup.R * (setup.S : ℝ) * (setup.cardX : ℝ) +
        C * Real.log setup.R * (setup.S : ℝ) * (setup.cardD : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hbound (le_of_lt hX_pos')
      have eq1 : C * Real.log setup.R *
          ((setup.S : ℝ) + (setup.S : ℝ) * (setup.cardD : ℝ) / (setup.cardX : ℝ)) *
          (setup.cardX : ℝ) =
          C * Real.log setup.R * (setup.S : ℝ) * (setup.cardX : ℝ) +
          C * Real.log setup.R * (setup.S : ℝ) * (setup.cardD : ℝ) := by
        have hX_ne : (setup.cardX : ℝ) ≠ 0 := ne_of_gt hX_pos'
        field_simp
      linarith
    have h2 : C * Real.log setup.R * (setup.S : ℝ) * 2 < (setup.cardX : ℝ) := by
      have := (div_lt_iff₀ hX_pos').mp h
      linarith
    nlinarith



end ProjectionTheory
