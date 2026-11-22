/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Finset BigOperators ENNReal

namespace BooleanFourier

noncomputable def fourierWeight {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (fourierCoeff f S ^ 2)

noncomputable def spectralDist {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (hf : ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1) :
    PMF (Finset (Fin n)) :=
  PMF.ofFintype (fun S => fourierWeight f S) (by
    simp only [fourierWeight]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => sq_nonneg (fourierCoeff f S))]
    rw [hf]
    exact ENNReal.ofReal_one)

end BooleanFourier
