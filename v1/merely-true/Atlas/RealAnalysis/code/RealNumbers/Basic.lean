/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace RealNumbers

/-- The real numbers `ℝ` form a strict ordered ring, contain `ℚ` via an injective ring
homomorphism, and satisfy the least upper bound property: every nonempty set bounded above
admits a least upper bound. -/
theorem real_numbers_theorem :
    IsStrictOrderedRing ℝ ∧
    Function.Injective (Rat.cast : ℚ → ℝ) ∧
    (∀ S : Set ℝ, S.Nonempty → BddAbove S → ∃ x, IsLUB S x) :=
  ⟨inferInstance, Rat.cast_injective, fun S hne hbdd => ⟨sSup S, Real.isLUB_sSup hne hbdd⟩⟩


/-- There exists a unique positive real number `r` with `r ^ 2 = 2`, namely `√2`; in particular
`√2 ∈ ℝ \ ℚ`. -/
theorem sqrt2_exists_unique : ∃! r : ℝ, 0 < r ∧ r ^ 2 = 2 := by
  refine ⟨Real.sqrt 2, ⟨Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2), ?_⟩, ?_⟩
  · rw [sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · intro y ⟨hy_pos, hy_sq⟩
    have h1 : y = Real.sqrt (y ^ 2) := by
      rw [Real.sqrt_sq hy_pos.le]
    rw [h1, hy_sq]

end RealNumbers
