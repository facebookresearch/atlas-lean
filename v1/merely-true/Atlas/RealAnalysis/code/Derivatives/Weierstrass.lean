/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- **Theorem II (reverse triangle inequality, three terms).** For all real numbers `a`, `b`, `c`,
the absolute value of their sum is at least `|a| - |b| - |c|`. -/
theorem reverse_triangle_three (a b c : ℝ) : |a + b + c| ≥ |a| - |b| - |c| := by
  have h1 : |a| - |b + c| ≤ |a + (b + c)| := abs_sub_abs_le_abs_add a (b + c)
  have h2 : |b + c| ≤ |b| + |c| := abs_add_le b c
  have h3 : a + (b + c) = a + b + c := by ring
  rw [h3] at h1
  linarith

open Real

/-- **Theorem I (cosine oscillation lemma).** Two statements about the cosine function:
(1) `cos` is 1-Lipschitz, i.e. `|cos x - cos y| ≤ |x - y|` for all real `x, y`.
(2) For every real `c` and every positive natural number `K`, there exists a point
`y` in the open interval `(c + π/K, c + 3π/K)` such that `|cos (K c) - cos (K y)| ≥ 1`. -/
theorem weierstrass_theorem_I :
    (∀ x y : ℝ, |cos x - cos y| ≤ |x - y|) ∧
    (∀ c : ℝ, ∀ K : ℕ, 0 < K →
      ∃ y, c + π / K < y ∧ y < c + 3 * π / K ∧
        |cos (K * c) - cos (K * y)| ≥ 1) := by
  refine ⟨abs_cos_sub_cos_le, fun c K hK => ?_⟩
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hK)
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hpi : (0 : ℝ) < π := pi_pos
  have h2K : (0 : ℝ) < 2 * (K : ℝ) := by linarith


  set y₁ := c + 3 * π / (2 * (K : ℝ))
  set y₂ := c + 5 * π / (2 * (K : ℝ))
  have hKy₁ : (K : ℝ) * y₁ = (K : ℝ) * c + 3 * π / 2 := by
    simp only [y₁]; field_simp
  have hKy₂ : (K : ℝ) * y₂ = (K : ℝ) * c + 5 * π / 2 := by
    simp only [y₂]; field_simp
  have hcos_y₁ : cos ((K : ℝ) * y₁) = sin ((K : ℝ) * c) := by
    rw [hKy₁]
    have h : (K : ℝ) * c + 3 * π / 2 = (K : ℝ) * c + π + π / 2 := by ring
    rw [h, cos_add_pi_div_two, sin_add_pi, neg_neg]
  have hcos_y₂ : cos ((K : ℝ) * y₂) = -sin ((K : ℝ) * c) := by
    rw [hKy₂]
    have h : (K : ℝ) * c + 5 * π / 2 = ((K : ℝ) * c + 2 * π) + π / 2 := by ring
    rw [h, cos_add_pi_div_two, sin_add_two_pi]
  have hy₁_lb : c + π / ↑K < y₁ := by
    simp only [y₁]
    have : π / (K : ℝ) < 3 * π / (2 * (K : ℝ)) := by
      rw [div_lt_div_iff₀ hKpos h2K]; nlinarith
    linarith
  have hy₁_ub : y₁ < c + 3 * π / ↑K := by
    simp only [y₁]
    have : 3 * π / (2 * (K : ℝ)) < 3 * π / (K : ℝ) := by
      apply div_lt_div_of_pos_left (by linarith : (0:ℝ) < 3 * π) hKpos (by linarith)
    linarith
  have hy₂_lb : c + π / ↑K < y₂ := by
    simp only [y₂]
    have : π / (K : ℝ) < 5 * π / (2 * (K : ℝ)) := by
      rw [div_lt_div_iff₀ hKpos h2K]; nlinarith
    linarith
  have hy₂_ub : y₂ < c + 3 * π / ↑K := by
    simp only [y₂]
    have : 5 * π / (2 * (K : ℝ)) < 3 * π / (K : ℝ) := by
      rw [div_lt_div_iff₀ h2K hKpos]; nlinarith
    linarith
  by_cases h : 1 ≤ |cos (↑K * c) - sin (↑K * c)|
  · exact ⟨y₁, hy₁_lb, hy₁_ub, by rw [hcos_y₁]; exact h⟩
  · push Not at h
    refine ⟨y₂, hy₂_lb, hy₂_ub, ?_⟩
    rw [hcos_y₂, sub_neg_eq_add]
    by_contra h2
    push Not at h2
    have key : (cos (↑K * c) - sin (↑K * c)) ^ 2 + (cos (↑K * c) + sin (↑K * c)) ^ 2 = 2 := by
      have := sin_sq_add_cos_sq (↑K * c)
      nlinarith
    have h3 : (cos (↑K * c) + sin (↑K * c)) ^ 2 < 1 := by
      have := abs_lt.mp (lt_of_lt_of_le h2 le_rfl)
      nlinarith
    have h4 : (cos (↑K * c) - sin (↑K * c)) ^ 2 < 1 := by
      have := abs_lt.mp (lt_of_lt_of_le h le_rfl)
      nlinarith
    linarith

open BigOperators Topology in
/-- The **Weierstrass nowhere-differentiable function**
`f(x) = ∑_{k=0}^∞ cos(160^k x) / 4^k`, defined as a `tsum` over the natural numbers. -/
noncomputable def weierstrass_fun (x : ℝ) : ℝ :=
  ∑' k : ℕ, cos (160 ^ k * x) / 4 ^ k

open BigOperators Topology in
/-- **Theorem III.** The defining series of the Weierstrass function is well-behaved:
(1) for every `x ∈ ℝ`, the series `∑ k, cos(160^k x) / 4^k` is absolutely convergent;
(2) the function `weierstrass_fun` is continuous and bounded on `ℝ`. -/
theorem weierstrass_theorem_III :
    (∀ x : ℝ, Summable (fun k : ℕ => |cos (160 ^ k * x) / 4 ^ k|)) ∧
    (Continuous weierstrass_fun ∧ ∃ B, ∀ x, |weierstrass_fun x| ≤ B) := by
  have summable_quarter : Summable (fun k : ℕ => (1/4 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have term_norm_le : ∀ k : ℕ, ∀ x : ℝ, ‖cos (160 ^ k * x) / 4 ^ k‖ ≤ (1/4 : ℝ) ^ k := by
    intro k x
    have h4pos : (0 : ℝ) < 4 ^ k := by positivity
    rw [norm_div]
    have h_norm_4k : ‖(4 : ℝ) ^ k‖ = 4 ^ k := by
      rw [Real.norm_eq_abs]; exact abs_of_pos h4pos
    rw [h_norm_4k]
    have h_cos_le : ‖cos (160 ^ k * x)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _
    calc ‖cos (160 ^ k * x)‖ / 4 ^ k
        ≤ 1 / 4 ^ k := div_le_div_of_nonneg_right h_cos_le (le_of_lt h4pos)
        _ = (1 / 4) ^ k := by rw [one_div, one_div, ← inv_pow]
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ summable_quarter
    intro k
    have := term_norm_le k x
    rwa [Real.norm_eq_abs] at this
  ·
    unfold weierstrass_fun
    exact continuous_tsum (u := fun k => (1/4 : ℝ) ^ k)
      (fun k => (continuous_cos.comp (continuous_const.mul continuous_id)).div_const _)
      summable_quarter (fun k x => term_norm_le k x)
  ·
    refine ⟨4/3, fun x => ?_⟩
    unfold weierstrass_fun
    rw [show |∑' k, cos (160 ^ k * x) / 4 ^ k| = ‖∑' k, cos (160 ^ k * x) / 4 ^ k‖ from
      (Real.norm_eq_abs _).symm]
    have hnorm_summ : Summable (fun k : ℕ => ‖cos (160 ^ k * x) / 4 ^ k‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => term_norm_le k x) summable_quarter
    calc ‖∑' k, cos (160 ^ k * x) / 4 ^ k‖
        ≤ ∑' k, ‖cos (160 ^ k * x) / 4 ^ k‖ := norm_tsum_le_tsum_norm hnorm_summ
        _ ≤ ∑' k : ℕ, (1/4 : ℝ) ^ k :=
            Summable.tsum_mono hnorm_summ summable_quarter (fun k => term_norm_le k x)
        _ = (1 - 1/4)⁻¹ := tsum_geometric_of_lt_one (by norm_num) (by norm_num)
        _ = 4/3 := by norm_num

open BigOperators Topology in
/-- For every real `x`, the series `∑ k, cos(160^k x) / 4^k` defining the Weierstrass function
is summable, by comparison with the geometric series `∑ (1/4)^k`. -/
lemma weierstrass_summable (x : ℝ) :
    Summable (fun k : ℕ => cos (160 ^ k * x) / (4:ℝ) ^ k) := by
  apply Summable.of_norm_bounded (g := fun k => (1/4 : ℝ) ^ k)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro k
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 4^k by positivity)]
    calc |cos (160 ^ k * x)| / (4 : ℝ) ^ k
        ≤ 1 / (4 : ℝ) ^ k := div_le_div_of_nonneg_right (abs_cos_le_one _) (by positivity)
      _ = (1/4) ^ k := by rw [one_div, ← inv_pow]; norm_num

open BigOperators Topology Filter in
/-- **Slope blow-up lemma.** For every real `c` and every natural number `n`, there exists a
point `y ≠ c` with `|y - c| < 3π / 160^n` such that the difference quotient of the
Weierstrass function between `y` and `c` has absolute value at least `40^n / (117 π)`.
Since `40^n / (117 π) → ∞`, this witnesses that the function cannot have a finite derivative
at `c`. -/
lemma weierstrass_slope_lower_bound (c : ℝ) (n : ℕ) :
    ∃ y : ℝ, y ≠ c ∧ |y - c| < 3 * π / (160:ℝ)^n ∧
    |(weierstrass_fun y - weierstrass_fun c) / (y - c)| ≥ (40:ℝ)^n / (117 * π) := by

  have hK : (0 : ℕ) < 160 ^ n := by positivity
  obtain ⟨y, hylb, hyub, hcos_osc⟩ := weierstrass_theorem_I.2 c (160^n) hK
  push_cast at hylb hyub hcos_osc
  have hpi_pos : (0:ℝ) < π := pi_pos
  have h160n_pos : (0:ℝ) < (160:ℝ)^n := by positivity
  have hymc_pos : 0 < y - c := by linarith [div_pos hpi_pos h160n_pos]
  have hymc_ub : y - c < 3 * π / (160:ℝ)^n := by linarith
  have hyne : y ≠ c := ne_of_gt (by linarith : c < y)
  have habs_yc : |y - c| = y - c := abs_of_pos hymc_pos
  refine ⟨y, hyne, by rw [habs_yc]; exact hymc_ub, ?_⟩


  rw [abs_div, habs_yc]

  rw [ge_iff_le, le_div_iff₀ hymc_pos]


  suffices hsuff : |weierstrass_fun y - weierstrass_fun c| ≥ 1 / (39 * (4:ℝ)^n) by
    have hcalc : (40:ℝ) ^ n / (117 * π) * (y - c)
        < (40:ℝ) ^ n / (117 * π) * (3 * π / (160:ℝ)^n) := by
      apply mul_lt_mul_of_pos_left hymc_ub
      exact div_pos (by positivity) (by linarith [pi_pos])
    have heq : (40:ℝ) ^ n / (117 * π) * (3 * π / (160:ℝ)^n) = 1 / (39 * (4:ℝ)^n) := by
      rw [show (160:ℝ)^n = (40:ℝ)^n * (4:ℝ)^n from by
        rw [show (160:ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
      field_simp; ring
    linarith [heq ▸ hcalc]

  set diff := fun k : ℕ => (cos ((160:ℝ) ^ k * y) - cos ((160:ℝ) ^ k * c)) / (4:ℝ) ^ k
  have hdiff_summable : Summable diff := by
    rw [show diff = (fun k => cos (160^k * y) / (4:ℝ)^k - cos (160^k * c) / (4:ℝ)^k) from by
      ext k; simp [diff]; ring]
    exact (weierstrass_summable y).sub (weierstrass_summable c)
  have hdiff_eq : weierstrass_fun y - weierstrass_fun c = ∑' k, diff k := by
    simp only [weierstrass_fun]
    rw [← (weierstrass_summable y).hasSum.sub (weierstrass_summable c).hasSum |>.tsum_eq]
    congr 1; ext k; simp [diff]; ring
  have hsplit : ∑' k, diff k = (∑ k ∈ Finset.range n, diff k) + diff n +
      ∑' k, diff (k + (n+1)) := by
    have htail : Summable (fun k => diff (k + (n+1))) :=
      hdiff_summable.comp_injective (fun a b h => by omega)
    have hkey := (hasSum_nat_add_iff (n+1)).mp htail.hasSum
    have huniq := hdiff_summable.hasSum.unique hkey
    rw [Finset.sum_range_succ] at huniq; linarith
  have ha : |diff n| ≥ 1 / (4:ℝ)^n := by
    simp only [diff, abs_div, abs_of_pos (show (0:ℝ) < (4:ℝ)^n by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ (4:ℝ)^n)
    rw [abs_sub_comm]; exact hcos_osc
  have hb : |∑ k ∈ Finset.range n, diff k| ≤ 4 / (13 * (4:ℝ)^n) := by
    calc |∑ k ∈ Finset.range n, diff k|
        ≤ ∑ k ∈ Finset.range n, |diff k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, (y - c) * (40:ℝ)^k := by
          apply Finset.sum_le_sum; intro k _
          simp only [diff, abs_div, abs_of_pos (show (0:ℝ) < (4:ℝ)^k by positivity)]
          calc |cos ((160:ℝ)^k * y) - cos ((160:ℝ)^k * c)| / (4:ℝ)^k
              ≤ ((160:ℝ)^k * (y - c)) / (4:ℝ)^k := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                calc |cos ((160:ℝ)^k * y) - cos ((160:ℝ)^k * c)|
                    ≤ |(160:ℝ)^k * y - (160:ℝ)^k * c| := abs_cos_sub_cos_le _ _
                  _ = (160:ℝ)^k * (y - c) := by
                      rw [show (160:ℝ)^k * y - (160:ℝ)^k * c = (160:ℝ)^k * (y - c) from by ring]
                      exact abs_of_pos (mul_pos (by positivity) hymc_pos)
            _ = (y - c) * (40:ℝ)^k := by
                rw [show (160:ℝ)^k = (40:ℝ)^k * (4:ℝ)^k from by
                  rw [show (160:ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
                have h4k : (4:ℝ)^k ≠ 0 := by positivity
                field_simp

      _ = (y - c) * ∑ k ∈ Finset.range n, (40:ℝ)^k := by rw [Finset.mul_sum]
      _ ≤ (3 * π / (160:ℝ)^n) * ((40:ℝ)^n / 39) := by
          apply mul_le_mul (le_of_lt hymc_ub) _ (by positivity) (by linarith [pi_pos])
          have hgeom := geom_sum_eq (show (40:ℝ) ≠ 1 from by norm_num) n
          linarith [show (0:ℝ) < (40:ℝ)^n from by positivity]
      _ = 3 * π / (39 * (4:ℝ)^n) := by
          rw [show (160:ℝ)^n = (40:ℝ)^n * (4:ℝ)^n from by
            rw [show (160:ℝ) = 40 * 4 from by norm_num]; rw [mul_pow]]
          field_simp

      _ ≤ 4 / (13 * (4:ℝ)^n) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 39 * (4:ℝ)^n)
            (by positivity : (0:ℝ) < 13 * (4:ℝ)^n)]
          nlinarith [pi_lt_four, show (0:ℝ) < (4:ℝ)^n from by positivity]

  have hc : |∑' k, diff (k + (n+1))| ≤ 2 / (3 * (4:ℝ)^n) := by
    have htail_summable : Summable (fun k => diff (k + (n+1))) :=
      hdiff_summable.comp_injective (fun a b h => by omega)
    have hterm_le : ∀ k, |diff (k + (n+1))| ≤ 2 / (4:ℝ)^(k + (n+1)) := by
      intro k
      simp only [diff, abs_div, abs_of_pos (show (0:ℝ) < (4:ℝ)^(k + (n+1)) by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ (4:ℝ)^(k + (n+1)))
      exact (abs_sub _ _).trans (by
        linarith [abs_cos_le_one (160^(k+(n+1)) * y), abs_cos_le_one (160^(k+(n+1)) * c)])
    have hsumm2 : Summable (fun k : ℕ => 2 / (4:ℝ)^(k + (n+1))) := by
      have heq2 : (fun k : ℕ => 2 / (4:ℝ)^(k + (n+1))) = (fun k => (2/(4:ℝ)^(n+1)) * ((4:ℝ)⁻¹)^k) := by
        ext k; rw [pow_add]; have h1 : (4:ℝ)^(n+1) ≠ 0 := by positivity
        have h2 : (4:ℝ)^k ≠ 0 := by positivity
        rw [show (4:ℝ)⁻¹^k = 1/(4:ℝ)^k from by rw [inv_pow, one_div]]; field_simp
      rw [heq2]; exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
    calc |∑' k, diff (k + (n+1))|
        ≤ ∑' k, |diff (k + (n+1))| := by
          exact le_of_eq_of_le (Real.norm_eq_abs _).symm
            (norm_tsum_le_tsum_norm htail_summable.norm)
      _ ≤ ∑' k : ℕ, 2 / (4:ℝ)^(k + (n+1)) := by
          apply Summable.tsum_mono htail_summable.norm hsumm2
          intro k; simp only [Real.norm_eq_abs]; exact hterm_le k
      _ = 2 / (3 * (4:ℝ)^n) := by
          have heq3 : ∀ k, 2 / (4:ℝ)^(k + (n+1)) = (2/(4:ℝ)^(n+1)) * ((4:ℝ)⁻¹)^k := by
            intro k; rw [pow_add]; have h1 : (4:ℝ)^(n+1) ≠ 0 := by positivity
            have h2 : (4:ℝ)^k ≠ 0 := by positivity
            rw [show (4:ℝ)⁻¹^k = 1/(4:ℝ)^k from by rw [inv_pow, one_div]]; field_simp
          simp_rw [heq3]
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (4:ℝ)⁻¹) (by norm_num)]
          rw [show (1:ℝ) - (4:ℝ)⁻¹ = 3/4 from by norm_num, show (3/4:ℝ)⁻¹ = 4/3 from by norm_num]
          rw [show (4:ℝ)^(n+1) = 4 * (4:ℝ)^n from by ring]; ring

  rw [hdiff_eq, hsplit]
  have hrt := reverse_triangle_three (diff n) (∑ k ∈ Finset.range n, diff k) (∑' k, diff (k + (n+1)))
  have hrearrange : ∑ k ∈ Finset.range n, diff k + diff n + ∑' k, diff (k + (n + 1)) =
      diff n + (∑ k ∈ Finset.range n, diff k) + ∑' k, diff (k + (n+1)) := by ring
  rw [hrearrange]
  linarith [show (1:ℝ)/(4:ℝ)^n - 4/(13*(4:ℝ)^n) - 2/(3*(4:ℝ)^n) = 1/(39*(4:ℝ)^n) from by
    field_simp; ring]

open BigOperators Topology Filter in
/-- **Weierstrass's theorem.** The function `weierstrass_fun x = ∑ k, cos(160^k x) / 4^k`
is nowhere differentiable on `ℝ`: for every `c`, `weierstrass_fun` fails to be differentiable
at `c`. The proof uses `weierstrass_slope_lower_bound` to exhibit a sequence of points
approaching `c` along which the difference quotients diverge to infinity, contradicting the
convergence of the slope to a finite derivative. -/
theorem weierstrass_nowhere_differentiable :
    ∀ c : ℝ, ¬ DifferentiableAt ℝ weierstrass_fun c := by
  intro c hdiff

  have hslope : Tendsto (slope weierstrass_fun c) (𝓝[≠] c) (𝓝 (deriv weierstrass_fun c)) :=
    hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt

  choose x hxne hxclose hxlarge using fun n => weierstrass_slope_lower_bound c n

  have hxc : Tendsto x atTop (𝓝 c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htend : Tendsto (fun n : ℕ => 3 * π / (160:ℝ)^n) atTop (𝓝 0) := by
      have : (fun n : ℕ => 3 * π / (160:ℝ)^n) = (fun n => (3 * π) * (1/160)^n) := by
        ext n; simp [div_eq_mul_inv, inv_pow]
      rw [this, show (0:ℝ) = (3 * π) * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds hε)).exists
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      calc |x n - c| < 3 * π / (160:ℝ)^n := hxclose n
        _ ≤ 3 * π / (160:ℝ)^N := by
            apply div_le_div_of_nonneg_left (by linarith [pi_pos]) (by positivity)
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 160) hn
        _ < ε := hN⟩

  have hslope_seq : Tendsto (fun n => slope weierstrass_fun c (x n)) atTop
      (𝓝 (deriv weierstrass_fun c)) := by
    apply hslope.comp
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hxc
      (eventually_atTop.mpr ⟨0, fun n _ => hxne n⟩)

  have hslope_norm : Tendsto (fun n => ‖slope weierstrass_fun c (x n)‖) atTop
      (𝓝 ‖deriv weierstrass_fun c‖) := hslope_seq.norm

  have hslope_eq : ∀ n, slope weierstrass_fun c (x n) =
      (weierstrass_fun (x n) - weierstrass_fun c) / (x n - c) := by
    intro n; simp [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
  have habs_large : ∀ n, ‖slope weierstrass_fun c (x n)‖ ≥ (40:ℝ)^n / (117 * π) := by
    intro n
    rw [Real.norm_eq_abs, hslope_eq]
    exact hxlarge n

  have h40_tendsto : Tendsto (fun n : ℕ => (40:ℝ)^n / (117 * π)) atTop atTop := by
    apply Filter.Tendsto.atTop_div_const (by linarith [pi_pos] : (0:ℝ) < 117 * π)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 40)

  have habs_tendsto : Tendsto (fun n => ‖slope weierstrass_fun c (x n)‖) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => habs_large n) h40_tendsto

  exact not_tendsto_atTop_of_tendsto_nhds hslope_norm habs_tendsto
