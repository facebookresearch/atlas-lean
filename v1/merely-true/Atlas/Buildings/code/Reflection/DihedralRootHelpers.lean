/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
import Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Theorems
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- For a unit vector $e$, the reflection formula simplifies to $\beta - 2⟨\beta,e⟩e$. -/
lemma linearReflection_unit (e β : E) (he : ‖e‖ = 1) :
    linearReflection e β = β - (2 * ⟪β, e⟫_ℝ) • e := by
  unfold linearReflection
  have h1 : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  rw [h1, div_one, real_inner_comm]

/-- Two non-parallel unit vectors have inner product of absolute value strictly less
than $1$. -/
lemma abs_inner_lt_one_of_not_parallel (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (h_not_par : ¬∃ c : ℝ, f = c • e) :
    |⟪e, f⟫_ℝ| < 1 := by
  rw [abs_lt]
  constructor
  ·
    by_contra h
    push Not at h
    have h1 := neg_one_le_real_inner_of_norm_eq_one he hf
    have h2 : ⟪e, f⟫_ℝ = -1 := le_antisymm h h1
    apply h_not_par
    have : ⟪e, -f⟫_ℝ = 1 := by rw [inner_neg_right, h2, neg_neg]
    have hne : ‖(-f)‖ = 1 := by rw [norm_neg, hf]
    have heq := (inner_eq_one_iff_of_norm_eq_one he hne).mp this
    exact ⟨-1, by rw [neg_smul, one_smul, heq, neg_neg]⟩
  ·
    rw [inner_lt_one_iff_real_of_norm_eq_one he hf]
    intro heq
    apply h_not_par
    exact ⟨1, by rw [heq, one_smul]⟩

end FiniteReflectionGroups
