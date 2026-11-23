/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ContinuousFunctions

/-- `AchievesAbsMin f S c` states that `f` achieves its absolute minimum on `S` at the point `c`,
i.e. `c ∈ S` and `f c ≤ f x` for every `x ∈ S`. -/
def AchievesAbsMin (f : ℝ → ℝ) (S : Set ℝ) (c : ℝ) : Prop :=
  c ∈ S ∧ ∀ x ∈ S, f c ≤ f x

/-- `AchievesAbsMax f S d` states that `f` achieves its absolute maximum on `S` at the point `d`,
i.e. `d ∈ S` and `f x ≤ f d` for every `x ∈ S`. -/
def AchievesAbsMax (f : ℝ → ℝ) (S : Set ℝ) (d : ℝ) : Prop :=
  d ∈ S ∧ ∀ x ∈ S, f x ≤ f d

/-- Continuity of `f` at a point `c ∈ S` (relative to `S`) is equivalent to the classical
`ε`-`δ` formulation: for every `ε > 0` there is `δ > 0` such that for all `x ∈ S`,
`|x - c| < δ` implies `|f x - f c| < ε`. -/
theorem continuous_at_iff_eps_delta (f : ℝ → ℝ) (S : Set ℝ) (c : ℝ) (_hc : c ∈ S) :
    ContinuousWithinAt f S c ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → |f x - f c| < ε := by
  rw [Metric.continuousWithinAt_iff]
  simp only [Real.dist_eq]

/-- `IsBoundedOn f S` states that `f` is bounded on `S`: there exists a nonnegative real
number `B` such that `|f x| ≤ B` for every `x ∈ S`. -/
def IsBoundedOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, |f x| ≤ B

/-- A real-valued function that is continuous on a closed bounded interval `[a, b]` is bounded:
there exists `B ∈ ℝ` such that `|f x| ≤ B` for all `x ∈ [a, b]`. -/
theorem continuous_on_Icc_bounded (f : ℝ → ℝ) (a b : ℝ) (_hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨C, fun x hx => by rw [← Real.norm_eq_abs]; exact hC x hx⟩

/-- Extreme Value (Min-Max) Theorem: a continuous function on a closed bounded interval `[a, b]`
attains both an absolute minimum at some point `c ∈ [a, b]` and an absolute maximum at some
point `d ∈ [a, b]`. -/
theorem extreme_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x) ∧
    (∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt hab)
  exact ⟨isCompact_Icc.exists_isMinOn hne hf, isCompact_Icc.exists_isMaxOn hne hf⟩

end ContinuousFunctions
