/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter Topology Polynomial

/-- **Weierstrass Approximation Theorem.** Every continuous real-valued function
`f` on a closed interval `[a, b]` is the uniform limit of a sequence of
polynomials: there exists `P : ℕ → ℝ[X]` such that `Polynomial.eval x (P n)`
converges to `f x` uniformly in `x ∈ [a, b]` as `n → ∞`. -/
theorem weierstrass_approximation {a b : ℝ} (f : C(Set.Icc a b, ℝ)) :
    ∃ P : ℕ → ℝ[X],
      TendstoUniformly (fun n (x : Set.Icc a b) => Polynomial.eval (x : ℝ) (P n)) f atTop := by
  have h : ∀ n : ℕ, ∃ p : ℝ[X], ‖p.toContinuousMapOn _ - f‖ < 1 / (↑n + 1) := by
    intro n
    exact exists_polynomial_near_continuousMap a b f _ (by positivity)
  choose P hP using h
  refine ⟨P, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro ε hε
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => fun x => ?_⟩
  have hPn := hP n
  have hpoint : ‖((P n).toContinuousMapOn (Set.Icc a b) - f) x‖ ≤
      ‖(P n).toContinuousMapOn (Set.Icc a b) - f‖ :=
    ContinuousMap.norm_coe_le_norm _ x
  simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply] at hpoint
  rw [dist_comm, Real.dist_eq]
  have h2 : (↑N : ℝ) + 1 > 0 := by positivity
  have h3 : (↑n : ℝ) + 1 ≥ (↑N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hNε : 1 / ((↑N : ℝ) + 1) < ε := by
    have : 1 < ε * (↑N + 1) := by
      have := (div_lt_iff₀ hε).mp hN
      linarith
    linarith [div_lt_iff₀ h2 |>.mpr this]
  calc |Polynomial.eval (↑x) (P n) - f x|
      _ ≤ ‖(P n).toContinuousMapOn (Set.Icc a b) - f‖ := by exact_mod_cast hpoint
      _ < 1 / (↑n + 1) := hPn
      _ ≤ 1 / (↑N + 1) := by
          apply div_le_div_of_nonneg_left one_pos.le h2 h3
      _ < ε := hNε
