/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.MajorityStablest

noncomputable section

open Finset BigOperators MeasureTheory ProbabilityTheory

namespace BooleanFourier

lemma isBooleanValued_hasBoundedRange {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : IsBooleanValued f) : HasBoundedRange f := by
  intro x
  rcases hf x with h | h <;> rw [h] <;> constructor <;> norm_num


end BooleanFourier

end
