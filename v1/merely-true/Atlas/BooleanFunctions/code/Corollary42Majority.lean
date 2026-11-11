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

theorem noiseSensitivity_majority_limit_pos
    (δ : ℝ) (hδ_pos : 0 < δ) :
    0 < (1 / Real.pi) * Real.arccos (1 - 2 * δ) := by
  apply mul_pos
  · exact div_pos one_pos Real.pi_pos
  · rw [Real.arccos_pos]
    linarith

end BooleanFourier
