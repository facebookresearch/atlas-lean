/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Complex MeasureTheory Set Metric Filter Topology NNReal

theorem differentiableAt_cauchy_transform
    {a : ℂ} {r : ℝ} {φ : ℂ → ℂ} (hr : 0 < r)
    (hint : CircleIntegrable φ a r)
    {z₀ : ℂ} (hz₀ : z₀ ∉ sphere a r) :
    DifferentiableAt ℂ (fun z => ∮ w in C(a, r), (z - w)⁻¹ * φ w) z₀ := by
  by_cases hball : z₀ ∈ ball a r
  ·
    suffices h : DifferentiableAt ℂ (fun z => ∮ w in C(a, r), (w - z)⁻¹ • φ w) z₀ by
      have heq : (fun z => ∮ w in C(a, r), (z - w)⁻¹ * φ w) =
          (fun z => -(∮ w in C(a, r), (w - z)⁻¹ • φ w)) := by
        ext z; simp only [smul_eq_mul]
        have : (fun w => (z - w)⁻¹ * φ w) = fun w => (-1) * ((w - z)⁻¹ * φ w) := by
          ext w; simp only [show z - w = -(w - z) from by ring, inv_neg, neg_mul, one_mul]
        rw [this, circleIntegral.integral_const_mul, neg_one_mul]
      rw [heq]; exact h.neg
    set R : NNReal := ⟨r, le_of_lt hr⟩
    have hps := hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R from hr)
    have hz₀' : z₀ ∈ eball a (R : ENNReal) := by rw [eball_coe]; exact hball
    have hdiff_g := (hps.analyticAt_of_mem hz₀').differentiableAt
    have h2pi_ne : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero _) I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    rw [show (fun z => ∮ w in C(a, r), (w - z)⁻¹ • φ w) =
        (2 * ↑Real.pi * I) • (fun z => (2 * ↑Real.pi * I)⁻¹ •
          ∮ w in C(a, r), (w - z)⁻¹ • φ w) from
      by ext z; simp only [Pi.smul_apply, smul_inv_smul₀ h2pi_ne]]
    exact hdiff_g.const_smul _
  ·
    have hd : r < dist z₀ a := by
      rw [mem_ball, not_lt] at hball; rw [mem_sphere] at hz₀
      exact lt_of_le_of_ne hball fun h => hz₀ h.symm
    set δ := (dist z₀ a - r) / 2 with hδ_def
    have hδ : 0 < δ := by linarith

    have hdist_lb : ∀ θ : ℝ, ∀ z ∈ ball z₀ δ, δ ≤ dist z (circleMap a r θ) := by
      intro θ z hz
      have h_on_circle : dist (circleMap a r θ) a = r := circleMap_mem_sphere a hr.le θ
      have h1 : dist z₀ a - r ≤ dist z₀ (circleMap a r θ) := by
        have := abs_dist_sub_le z₀ (circleMap a r θ) a
        rw [h_on_circle] at this; linarith [abs_le.mp this]
      have h2 : 2 * δ ≤ dist z₀ (circleMap a r θ) := by linarith
      have h3 : dist z z₀ < δ := mem_ball.mp hz
      linarith [dist_triangle z₀ z (circleMap a r θ), dist_comm z₀ z]
    have hne : ∀ θ : ℝ, ∀ z ∈ ball z₀ δ, z ≠ circleMap a r θ := by
      intro θ z hz habs
      have := hdist_lb θ z hz
      rw [habs, dist_self] at this; linarith

    set F : ℂ → ℝ → ℂ := fun z θ =>
      deriv (circleMap a r) θ • ((z - circleMap a r θ)⁻¹ * φ (circleMap a r θ))
    set F' : ℂ → ℝ → ℂ := fun z θ =>
      deriv (circleMap a r) θ •
        ((-1 / (z - circleMap a r θ) ^ 2) * φ (circleMap a r θ))

    have hFdef : ∀ z, (∮ w in C(a, r), (z - w)⁻¹ * φ w) =
        ∫ θ in (0:ℝ)..(2 * Real.pi), F z θ := fun _ => rfl
    simp_rw [hFdef]

    have hF_ii : ∀ x ∈ ball z₀ δ, IntervalIntegrable (F x) volume 0 (2 * Real.pi) := by
      intro x hx
      have heq : F x = fun θ => (x - circleMap a r θ)⁻¹ *
          (deriv (circleMap a r) θ • φ (circleMap a r θ)) := by
        ext θ; simp only [F, smul_eq_mul]; ring
      rw [heq]
      exact hint.out.continuousOn_mul
        ((continuous_const.sub (continuous_circleMap a r)).inv₀
          (fun θ => sub_ne_zero.mpr (hne θ x hx))).continuousOn
    have hF'_ii : ∀ x ∈ ball z₀ δ, IntervalIntegrable (F' x) volume 0 (2 * Real.pi) := by
      intro x hx
      have heq : F' x = fun θ => (-1 / (x - circleMap a r θ) ^ 2) *
          (deriv (circleMap a r) θ • φ (circleMap a r θ)) := by
        ext θ; simp only [F', smul_eq_mul]; ring
      rw [heq]
      exact hint.out.continuousOn_mul
        (Continuous.continuousOn (Continuous.div continuous_const
          ((continuous_const.sub (continuous_circleMap a r)).pow 2)
          (fun θ => pow_ne_zero 2 (sub_ne_zero.mpr (hne θ x hx)))))

    have key := @intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      ℂ _ volume ℂ _ _ _ 0 (2 * Real.pi)
      (fun θ => (1/δ^2) * ‖deriv (circleMap a r) θ • φ (circleMap a r θ)‖)
      F F' z₀ (ball z₀ δ)
      (ball_mem_nhds z₀ hδ)
      ?hF_meas ?hF_int ?hF'_meas ?h_bound ?bound_int ?h_diff
    · exact key.2.differentiableAt
    case hF_meas =>
      apply eventually_of_mem (ball_mem_nhds z₀ hδ)
      intro x hx
      rw [uIoc_of_le (by positivity)]
      exact (hF_ii x hx).1.aestronglyMeasurable
    case hF_int =>
      exact hF_ii z₀ (mem_ball_self hδ)
    case hF'_meas =>
      rw [uIoc_of_le (by positivity)]
      exact (hF'_ii z₀ (mem_ball_self hδ)).1.aestronglyMeasurable
    case h_bound =>
      apply Filter.Eventually.of_forall
      intro θ hθ x hx
      simp only [F', norm_smul]
      have key : ‖(-1 : ℂ) / (x - circleMap a r θ) ^ 2‖ ≤ 1 / δ ^ 2 := by
        rw [norm_div, norm_neg, norm_one, norm_pow, one_div, one_div]
        gcongr
        have h := hdist_lb θ x hx
        rwa [← dist_eq_norm]
      calc ‖deriv (circleMap a r) θ‖ *
            ‖(-1 / (x - circleMap a r θ) ^ 2) * φ (circleMap a r θ)‖
          = ‖deriv (circleMap a r) θ‖ *
            (‖(-1 : ℂ) / (x - circleMap a r θ) ^ 2‖ * ‖φ (circleMap a r θ)‖) := by
            rw [norm_mul]
        _ ≤ ‖deriv (circleMap a r) θ‖ * (1 / δ ^ 2 * ‖φ (circleMap a r θ)‖) := by gcongr
        _ = 1 / δ ^ 2 * (‖deriv (circleMap a r) θ‖ * ‖φ (circleMap a r θ)‖) := by ring
    case bound_int =>
      exact (hint.out.norm).const_mul _
    case h_diff =>
      apply Filter.Eventually.of_forall
      intro θ hθ x hx
      have hxne : x ≠ circleMap a r θ := hne θ x hx
      show HasDerivAt (fun z => F z θ) (F' x θ) x
      show HasDerivAt (fun z => deriv (circleMap a r) θ •
          ((z - circleMap a r θ)⁻¹ * φ (circleMap a r θ)))
        (deriv (circleMap a r) θ •
          ((-1 / (x - circleMap a r θ) ^ 2) * φ (circleMap a r θ))) x
      have h1 : HasDerivAt (fun z => z - circleMap a r θ) 1 x :=
        (hasDerivAt_id x).sub_const _
      have h2 := h1.inv (sub_ne_zero.mpr hxne)
      exact (h2.mul_const (φ (circleMap a r θ))).const_smul (deriv (circleMap a r) θ)
