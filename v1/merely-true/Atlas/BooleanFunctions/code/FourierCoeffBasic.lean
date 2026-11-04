/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Parseval
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.NoiseStability

open Finset BigOperators

namespace BooleanFourier

theorem noiseOp_preserves_expectation {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    fourierCoeff (noiseOperator ρ f) ∅ = fourierCoeff f ∅ := by
  rw [fourierCoeff_noiseOperator]
  simp [Finset.card_empty]

end BooleanFourier
