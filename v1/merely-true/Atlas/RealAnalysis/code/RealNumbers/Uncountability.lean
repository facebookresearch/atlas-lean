/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Real.Cardinality

namespace RealNumbers

/-- Cantor's theorem: the half-open interval `(0, 1]` of real numbers is uncountable. -/
theorem Ioc_zero_one_uncountable : ¬ Set.Countable (Set.Ioc (0:ℝ) 1) := by
  rw [← Cardinal.le_aleph0_iff_set_countable, not_le]
  rw [Cardinal.mk_Ioc_real (by norm_num : (0:ℝ) < 1)]
  exact Cardinal.aleph0_lt_continuum

/-- Corollary of Cantor's theorem: the set of real numbers `ℝ` is uncountable. -/
theorem real_uncountable : ¬ Set.Countable (Set.univ : Set ℝ) :=
  Cardinal.not_countable_real

end RealNumbers
