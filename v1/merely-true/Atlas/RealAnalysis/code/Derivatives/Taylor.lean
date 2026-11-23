/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

/-- A real-valued function `f` is `n`-times differentiable on the set `S` if `S` has the unique
differentiability property and, for every `m < n`, the `m`-th iterated derivative of `f` within
`S` is itself differentiable on `S`. Equivalently, the derivatives `f', f'', …, f^{(n)}` all exist
at every point of `S`. -/
def IsNTimesDiffOn (f : ℝ → ℝ) (n : ℕ) (S : Set ℝ) : Prop :=
  UniqueDiffOn ℝ S ∧ ∀ m < n, DifferentiableOn ℝ (iteratedDerivWithin m f S) S

/-- The `n`-th order Taylor polynomial of `f` centered at `x₀`, evaluated at `x`:
`P_n(x) = ∑_{k=0}^{n} f^{(k)}(x₀) / k! · (x - x₀)^k`. -/
noncomputable def taylorPolynomial (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k f x₀ / k.factorial) * (x - x₀) ^ k

/-- **Taylor's theorem** (Lagrange form of the remainder). Suppose `f : ℝ → ℝ` is `n` times
continuously differentiable on `[x₀, x]` and its `n`-th derivative is differentiable on the open
interval `(x₀, x)`. Then there exists `c ∈ (x₀, x)` such that
`f(x) = ∑_{k=0}^{n} f^{(k)}(x₀)/k! · (x - x₀)^k + f^{(n+1)}(c)/(n+1)! · (x - x₀)^{n+1}`.
That is, `f(x)` equals the `n`-th order Taylor polynomial at `x₀` plus the Lagrange remainder
term evaluated at some intermediate point `c`. -/
theorem taylor_theorem (f : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) (hx : x₀ < x)
    (hf : ContDiffOn ℝ (↑n) f (Set.Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.Icc x₀ x)) (Set.Ioo x₀ x)) :
    ∃ c ∈ Set.Ioo x₀ x,
      f x = (∑ k ∈ Finset.range (n + 1),
          iteratedDerivWithin k f (Set.Icc x₀ x) x₀ / k.factorial * (x - x₀) ^ k) +
        iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c / (n + 1).factorial *
          (x - x₀) ^ (n + 1) := by
  obtain ⟨c, hc_mem, hc_eq⟩ := taylor_mean_remainder_lagrange hx hf hf'
  refine ⟨c, hc_mem, ?_⟩
  rw [taylor_within_apply] at hc_eq
  have hsum_eq : (∑ k ∈ Finset.range (n + 1),
      ((↑k.factorial)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f (Set.Icc x₀ x) x₀) =
    (∑ k ∈ Finset.range (n + 1),
      iteratedDerivWithin k f (Set.Icc x₀ x) x₀ / ↑k.factorial * (x - x₀) ^ k) := by
    congr 1; ext k; simp [smul_eq_mul, div_eq_inv_mul]; ring
  linarith [show iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c * (x - x₀) ^ (n + 1) /
      ↑(n + 1).factorial = iteratedDerivWithin (n + 1) f (Set.Icc x₀ x) c /
      ↑(n + 1).factorial * (x - x₀) ^ (n + 1) from by ring]

/-- A function `f : ℝ → ℝ` has a strict local (relative) minimum at `x₀` if `f x₀ < f x` for all
`x` sufficiently close to but distinct from `x₀`. -/
def IsStrictLocalMin (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, f x₀ < f x

/-- **Second derivative test for a strict local minimum.** If `f : ℝ → ℝ` is twice continuously
differentiable at `x₀`, with `f'(x₀) = 0` and `f''(x₀) > 0`, then `f` has a strict relative
minimum at `x₀`. -/
theorem second_derivative_test_min (f : ℝ → ℝ) (x₀ : ℝ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (hf1 : deriv f x₀ = 0) (hf2 : 0 < iteratedDeriv 2 f x₀) :
    IsStrictLocalMin f x₀ := by
  have h2 : deriv (deriv f) x₀ > 0 := by
    simp only [iteratedDeriv_succ] at hf2; exact hf2
  have hsign : ∀ᶠ x in nhds x₀, SignType.sign (deriv f x) = SignType.sign (x - x₀) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos h2 hf1
  rw [Metric.eventually_nhds_iff] at hsign
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := hsign
  have h1 : ContDiffAt ℝ 1 f x₀ := hf.of_le (by norm_num)
  rw [contDiffAt_one_iff] at h1
  obtain ⟨f', u, hu_nhds, _, hfderiv⟩ := h1
  rw [Metric.mem_nhds_iff] at hu_nhds
  obtain ⟨ε₂, hε₂_pos, hball_u⟩ := hu_nhds
  set r := min ε₁ ε₂
  have hr_pos : 0 < r := lt_min hε₁_pos hε₂_pos
  have hdiff_ball : ∀ z, dist z x₀ < r → DifferentiableAt ℝ f z := by
    intro z hz
    exact (hfderiv z (hball_u (Metric.mem_ball.mpr
      (lt_of_lt_of_le hz (min_le_right _ _))))).differentiableAt
  have hsign_ball : ∀ z, dist z x₀ < r →
      SignType.sign (deriv f z) = SignType.sign (z - x₀) := by
    intro z hz; exact hε₁ (lt_of_lt_of_le hz (min_le_left _ _))
  have hdist_between_left : ∀ y z, y < x₀ → dist y x₀ < r →
      z ∈ Set.Icc y x₀ → dist z x₀ < r := by
    intro y z hlt hy hz
    rw [Real.dist_eq] at hy ⊢
    rw [abs_of_nonpos (by linarith : y - x₀ ≤ 0)] at hy
    rw [abs_of_nonpos (by linarith [hz.2] : z - x₀ ≤ 0)]
    linarith [hz.1]
  have hdist_between_right : ∀ y z, x₀ < y → dist y x₀ < r →
      z ∈ Set.Icc x₀ y → dist z x₀ < r := by
    intro y z hgt hy hz
    rw [Real.dist_eq] at hy ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ y - x₀)] at hy
    rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z - x₀)]
    linarith [hz.2]
  show ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, f x₀ < f x
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨r, hr_pos, fun {y} hy hyne => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyne
  rcases lt_or_gt_of_ne hyne with hlt | hgt
  ·
    have hcont : ContinuousOn f (Set.Icc y x₀) := fun z hz =>
      (hdiff_ball z (hdist_between_left y z hlt hy hz)).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn f (Set.Icc y x₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y x₀) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz_r := hdist_between_left y z hlt hy (Set.Ioo_subset_Icc_self hz)
      have hsz := hsign_ball z hz_r
      rw [sign_neg (by linarith [hz.2] : z - x₀ < 0)] at hsz
      exact sign_eq_neg_one_iff.mp hsz
    exact hanti (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt
  ·
    have hcont : ContinuousOn f (Set.Icc x₀ y) := fun z hz =>
      (hdiff_ball z (hdist_between_right y z hgt hy hz)).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn f (Set.Icc x₀ y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x₀ y) hcont
      intro z hz
      rw [interior_Icc] at hz
      have hz_r := hdist_between_right y z hgt hy (Set.Ioo_subset_Icc_self hz)
      have hsz := hsign_ball z hz_r
      rw [sign_pos (by linarith [hz.1] : 0 < z - x₀)] at hsz
      exact sign_eq_one_iff.mp hsz
    exact hmono (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt
