/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.DifferentialGeometry.code.ClosedCurves

open MeasureTheory Real Set Filter Topology

namespace SturmHurwitz

lemma sin_half_diff_ne_zero {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Ico 0 (2 * π)) (ht₂ : t₂ ∈ Ico 0 (2 * π))
    (hne : t₁ ≠ t₂) : sin ((t₁ - t₂) / 2) ≠ 0 := by
  rw [sin_ne_zero_iff]
  intro n hn
  have hn0 : n = 0 := by
    have : (-1 : ℤ) < n := by
      by_contra h; push Not at h
      have : (n : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [ht₁.1, ht₂.2, pi_pos]
    have : n < (1 : ℤ) := by
      by_contra h; push Not at h
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith [ht₁.2, ht₂.1, pi_pos]
    omega
  simp [hn0] at hn; exact hne (by linarith)


lemma periodic_deriv (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
    ∀ t, deriv g (t + 2 * Real.pi) = deriv g t := by
  intro t
  have lhs : HasDerivAt (fun s => g (s + 2 * π)) (deriv g (t + 2 * π)) t :=
    ((hdiff (t + 2 * π)).hasDerivAt.comp t ((hasDerivAt_id t).add_const (2 * π))).congr_deriv
      (by ring) |>.congr_of_eventuallyEq (by filter_upwards with s; simp [Function.comp])
  rw [show (fun s => g (s + 2 * π)) = g from funext hper] at lhs
  exact lhs.unique (hdiff t).hasDerivAt

lemma ibp_deriv_cos (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hcont_g' : Continuous (deriv g)) (hcont_g : Continuous g)
    (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
    ∫ t in (0:ℝ)..(2*π), deriv g t * cos t = ∫ t in (0:ℝ)..(2*π), g t * sin t := by
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_cos x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_sin.neg.intervalIntegrable 0 (2*π))
  simp only [cos_two_pi, cos_zero, mul_one] at ibp
  have hper0 : g (2 * π) = g 0 := by have := hper 0; simp only [zero_add] at this; exact this
  rw [hper0, sub_self] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * cos x + g x * (-sin x) =
    (∫ x in (0:ℝ)..(2*π), deriv g x * cos x) + (∫ x in (0:ℝ)..(2*π), g x * (-sin x)) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_cos).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_sin.neg).intervalIntegrable 0 (2*π))
  have hneg : ∫ x in (0:ℝ)..(2*π), g x * (-sin x) = -(∫ x in (0:ℝ)..(2*π), g x * sin x) := by
    have : (fun x => g x * (-sin x)) = fun x => -(g x * sin x) := by ext; ring
    rw [this, intervalIntegral.integral_neg]
  linarith [hsplit, hneg]

lemma ibp_deriv_sin (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hcont_g' : Continuous (deriv g)) (hcont_g : Continuous g) :
    ∫ t in (0:ℝ)..(2*π), deriv g t * sin t = -(∫ t in (0:ℝ)..(2*π), g t * cos t) := by
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_sin x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_cos.intervalIntegrable 0 (2*π))
  simp only [sin_two_pi, sin_zero, mul_zero, sub_zero] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * sin x + g x * cos x =
    (∫ x in (0:ℝ)..(2*π), deriv g x * sin x) + (∫ x in (0:ℝ)..(2*π), g x * cos x) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_sin).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_cos).intervalIntegrable 0 (2*π))
  linarith [hsplit]


end SturmHurwitz

namespace FourVertex

open Real ClosedCurves






end FourVertex
