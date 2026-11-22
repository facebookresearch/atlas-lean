/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace MultiplicativeConvolution

variable {G : Type*} [Fintype G] [Group G]

/-- Multiplicative (group) convolution of two functions `f, g : G → ℂ` on a finite group `G`,
defined by `(f *_M g)(a) = ∑_{b ∈ G} f(b) · g(a · b⁻¹)`. -/
def mulConv (f g : G → ℂ) (a : G) : ℂ :=
  ∑ b : G, f b * g (a * b⁻¹)

/-- The $L^2$ norm of a function `f : G → ℂ` on a finite group, i.e. `‖f‖₂ = √(∑_b ‖f b‖²)`. -/
def l2Norm (f : G → ℂ) : ℝ :=
  Real.sqrt (∑ b : G, ‖f b‖ ^ 2)

/-- For a fixed `a ∈ G`, the map `b ↦ a · b⁻¹` is a bijection of `G` to itself. This is used
to reindex sums in convolution estimates. -/
def mulInvEquiv (a : G) : G ≃ G where
  toFun b := a * b⁻¹
  invFun b := (a⁻¹ * b)⁻¹
  left_inv b := by simp
  right_inv b := by simp

/-- Pointwise bound on multiplicative convolution: by Cauchy–Schwarz,
`‖(f *_M g)(a)‖ ≤ ‖f‖₂ · ‖g‖₂` for every `a ∈ G`. -/
theorem norm_mulConv_le (f g : G → ℂ) (a : G) :
    ‖mulConv f g a‖ ≤ l2Norm f * l2Norm g := by
  unfold mulConv l2Norm
  have hreindex : ∑ b : G, ‖g (a * b⁻¹)‖ ^ 2 = ∑ b : G, ‖g b‖ ^ 2 :=
    Fintype.sum_equiv (mulInvEquiv a) _ _ (fun _ => rfl)
  calc ‖∑ b : G, f b * g (a * b⁻¹)‖
      ≤ ∑ b : G, ‖f b * g (a * b⁻¹)‖ := norm_sum_le _ _
    _ = ∑ b : G, ‖f b‖ * ‖g (a * b⁻¹)‖ := by
        congr 1; ext b; exact norm_mul _ _
    _ ≤ Real.sqrt (∑ b : G, ‖f b‖ ^ 2) * Real.sqrt (∑ b : G, ‖g (a * b⁻¹)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ b : G, ‖f b‖ ^ 2) * Real.sqrt (∑ b : G, ‖g b‖ ^ 2) := by
        rw [hreindex]

/-- $L^\infty$ form of the convolution bound: `‖f *_M g‖_{L^∞} ≤ ‖f‖₂ · ‖g‖₂`. This is
Lemma 2 from BKT's Subsection 7.3 (Multiplicative Convolution and Projections). -/
theorem linftyNorm_mulConv_le (f g : G → ℂ) :
    (⨆ a : G, ‖mulConv f g a‖) ≤ l2Norm f * l2Norm g := by
  apply ciSup_le
  exact norm_mulConv_le f g

end MultiplicativeConvolution
