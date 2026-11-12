/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Claim21Lec10
import Atlas.BooleanFunctions.code.DisagreementStability
open Finset BigOperators Real Filter

namespace BooleanFourier

theorem noiseSensitivity_majority_limit_lt_half
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 / 2) :
    (1 / Real.pi) * Real.arccos (1 - 2 * δ) < 1 / 2 := by
  have h1 : (0 : ℝ) < 1 - 2 * δ := by linarith
  have h3 : Real.arccos (1 - 2 * δ) < Real.pi / 2 := by
    rw [show Real.pi / 2 = Real.arccos 0 from (Real.arccos_zero).symm]
    exact Real.arccos_lt_arccos (by linarith : (-1 : ℝ) ≤ 0) h1
      (by linarith : (1 : ℝ) - 2 * δ ≤ 1)
  calc (1 / Real.pi) * Real.arccos (1 - 2 * δ)
      < (1 / Real.pi) * (Real.pi / 2) := by
        apply mul_lt_mul_of_pos_left h3
        exact div_pos one_pos Real.pi_pos
    _ = 1 / 2 := by field_simp

end BooleanFourier
