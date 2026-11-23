/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HasseMinkowski

/-- Generic expansion of the 3-variable weighted sum of squares over any commutative
semiring $k$. -/
lemma wss_vec3_generic {k : Type*} [CommSemiring k] (w₀ w₁ w₂ x₀ x₁ x₂ : k) :
    QuadraticMap.weightedSumSquares k ![w₀, w₁, w₂] ![x₀, x₁, x₂] =
    w₀ * (x₀ * x₀) + w₁ * (x₁ * x₁) + w₂ * (x₂ * x₂) := by
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul]

/-- Specialization of `wss_vec3_generic` to the real numbers. -/
lemma wss_vec3 (w₀ w₁ w₂ x₀ x₁ x₂ : ℝ) :
    QuadraticMap.weightedSumSquares ℝ ![w₀, w₁, w₂] ![x₀, x₁, x₂] =
    w₀ * (x₀ * x₀) + w₁ * (x₁ * x₁) + w₂ * (x₂ * x₂) :=
  wss_vec3_generic w₀ w₁ w₂ x₀ x₁ x₂

/-- The triple $[a, b, c]$ is nonzero if its first component is. -/
lemma vec3_ne_zero_of_idx0 {α : Type*} [Zero α] (a b c : α) (ha : a ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact ha (by have := congr_fun h 0; simpa using this)

/-- The triple $[a, b, c]$ is nonzero if its second component is. -/
lemma vec3_ne_zero_of_idx1 {α : Type*} [Zero α] (a b c : α) (hb : b ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact hb (by have := congr_fun h 1; simpa using this)

/-- The triple $[a, b, c]$ is nonzero if its third component is. -/
lemma vec3_ne_zero_of_idx2 {α : Type*} [Zero α] (a b c : α) (hc : c ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact hc (by have := congr_fun h 2; simpa using this)
