/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ContinuousFunctions

open Set

/-- Bolzano's Intermediate Value Theorem.

Let `f : ℝ → ℝ` be continuous on `[a, b]` with `a < b`. Then:
* if `f a < y < f b`, there exists `c ∈ (a, b)` with `f c = y`;
* if `f b < y < f a`, there exists `c ∈ (a, b)` with `f c = y`.

In either case, `f` attains every value strictly between `f a` and `f b` at some
interior point of the interval. -/
theorem intermediate_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∀ y, f a < y → y < f b → ∃ c ∈ Set.Ioo a b, f c = y) ∧
    (∀ y, f b < y → y < f a → ∃ c ∈ Set.Ioo a b, f c = y) := by
  have hab' : a ≤ b := le_of_lt hab
  constructor
  · intro y hy1 hy2
    have hy_mem : y ∈ Icc (f a) (f b) := ⟨le_of_lt hy1, le_of_lt hy2⟩
    obtain ⟨c, hc_mem, hfc⟩ := intermediate_value_Icc hab' hf hy_mem
    refine ⟨c, ?_, hfc⟩
    constructor
    · rcases eq_or_lt_of_le hc_mem.1 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy1]
      · exact h
    · rcases eq_or_lt_of_le hc_mem.2 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy2]
      · exact h
  · intro y hy1 hy2
    have hy_mem : y ∈ Icc (f b) (f a) := ⟨le_of_lt hy1, le_of_lt hy2⟩
    obtain ⟨c, hc_mem, hfc⟩ := intermediate_value_Icc' hab' hf hy_mem
    refine ⟨c, ?_, hfc⟩
    constructor
    · rcases eq_or_lt_of_le hc_mem.1 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy2]
      · exact h
    · rcases eq_or_lt_of_le hc_mem.2 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy1]
      · exact h

/-- The polynomial `f(x) = x^2021 + x^2020 + 9.03 x + 1` has at least one real
root.

Proved via the Intermediate Value Theorem: `f(-1) < 0` and `f(0) > 0`, so by
continuity there exists `c ∈ [-1, 0]` with `f(c) = 0`. -/
theorem polynomial_has_real_root : ∃ x : ℝ, x^2021 + x^2020 + 9.03*x + 1 = 0 := by

  let f : ℝ → ℝ := fun x => x^2021 + x^2020 + 9.03*x + 1

  have hf_cont : Continuous f := by fun_prop

  have hf_neg : f (-1) < 0 := by norm_num [f]

  have hf_pos : (0 : ℝ) < f 0 := by norm_num [f]

  have hab : (-1 : ℝ) ≤ 0 := by norm_num
  have h0_mem : (0 : ℝ) ∈ Icc (f (-1)) (f 0) :=
    ⟨le_of_lt hf_neg, le_of_lt hf_pos⟩
  have h_ivt := intermediate_value_Icc hab hf_cont.continuousOn h0_mem
  obtain ⟨c, _, hfc⟩ := h_ivt
  exact ⟨c, hfc⟩

end ContinuousFunctions
