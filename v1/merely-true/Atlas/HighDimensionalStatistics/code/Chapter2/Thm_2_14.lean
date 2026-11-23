/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_6
import Atlas.HighDimensionalStatistics.code.Chapter2.Lemma_2_7
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_14_SubspaceBound
import Mathlib

open Matrix Finset BigOperators Rigollet MeasureTheory

/-- Deterministic step of Theorem 2.14: given a BIC estimator `θ̂` with penalty
`τ²·‖θ‖₀` and the noise-control hypothesis
`4 (⟨ε, X(θ - θ*)⟩)² ≤ ‖X(θ - θ*)‖² · (2n τ² ‖θ‖₀ + t)` for all `θ`, one obtains
the deterministic prediction error bound
`‖X(θ̂ - θ*)‖² ≤ 2 n τ² ‖θ*‖₀ + t`. -/
theorem thm_2_14_bic_bound
    {n d : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (θstar : Fin d → ℝ) (eps : Fin n → ℝ)
    (hY : Y = X.mulVec θstar + eps)
    (τ : ℝ) (_hτ : 0 < τ)
    (θhat : Fin d → ℝ)
    (hBIC : IsBICEstimatorL2 X Y τ θhat)
    (t : ℝ) (ht : 0 ≤ t)


    (hnoise : ∀ (θ : Fin d → ℝ),
      4 * (dotProduct eps (X.mulVec (θ - θstar))) ^ 2 ≤
        dotProduct (X.mulVec (θ - θstar)) (X.mulVec (θ - θstar)) *
        (2 * ↑n * τ ^ 2 * (l0norm θ : ℝ) + t)) :
    dotProduct (X.mulVec (θhat - θstar)) (X.mulVec (θhat - θstar)) ≤
      2 * ↑n * τ ^ 2 * (l0norm θstar : ℝ) + t := by

  have h1 := hBIC.2 θstar
  subst hY

  have hres : (X.mulVec θstar + eps) - X.mulVec θhat = eps - X.mulVec (θhat - θstar) := by
    ext i; simp [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]; ring
  have hres_star : (X.mulVec θstar + eps) - X.mulVec θstar = eps := by
    ext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [hres, hres_star] at h1

  set δ := X.mulVec (θhat - θstar) with hδ_def
  have hexpand : sqL2norm (eps - δ) = sqL2norm eps - 2 * ∑ i, eps i * δ i + sqL2norm δ := by
    simp only [sqL2norm, Pi.sub_apply]
    simp_rw [fun i : Fin n =>
      show (eps i - δ i) ^ 2 = eps i ^ 2 - 2 * (eps i * δ i) + δ i ^ 2 from by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand] at h1

  have hD_eq : dotProduct δ δ = sqL2norm δ := by
    simp [sqL2norm, dotProduct]; congr 1; ext i; ring
  have hB_eq : dotProduct eps δ = ∑ i, eps i * δ i := by simp [dotProduct]

  set D := dotProduct δ δ with hD_def
  set B := dotProduct eps δ with hB_def2
  set a := ↑n * τ ^ 2 * (l0norm θhat : ℝ) with ha_def
  set b := ↑n * τ ^ 2 * (l0norm θstar : ℝ) with hb_def
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn

  have hD_nn : 0 ≤ D := by
    simp only [D, dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a := δ i))

  have hb_nn : 0 ≤ b := by
    simp only [hb_def]
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg' n) (sq_nonneg τ)) (Nat.cast_nonneg' (l0norm θstar))


  have hBIC_r : D ≤ 2 * B + b - a := by
    rw [hD_eq, hB_eq]
    show sqL2norm δ ≤ 2 * (∑ i, eps i * δ i) + b - a
    have key : 1 / ↑n * sqL2norm δ ≤ 1 / ↑n * (2 * (∑ i, eps i * δ i)) +
        (τ ^ 2 * (l0norm θstar : ℝ) - τ ^ 2 * (l0norm θhat : ℝ)) := by
      nlinarith [show 1 / (↑n : ℝ) * (sqL2norm eps - 2 * (∑ i, eps i * δ i) + sqL2norm δ) =
        1 / ↑n * sqL2norm eps - 1 / ↑n * (2 * (∑ i, eps i * δ i)) + 1 / ↑n * sqL2norm δ
          from by ring]
    have h2 : sqL2norm δ ≤ ↑n * (1 / ↑n * (2 * (∑ i, eps i * δ i)) +
        (τ ^ 2 * (l0norm θstar : ℝ) - τ ^ 2 * (l0norm θhat : ℝ))) := by
      calc sqL2norm δ = ↑n * (1 / ↑n * sqL2norm δ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left key (le_of_lt hn_pos)
    have h3 : ↑n * (1 / ↑n * (2 * (∑ i, eps i * δ i)) +
        (τ ^ 2 * ↑(l0norm θstar) - τ ^ 2 * ↑(l0norm θhat))) =
      2 * (∑ i, eps i * δ i) + b - a := by
      simp only [ha_def, hb_def]; field_simp; ring
    linarith

  have hnoise' : 4 * B ^ 2 ≤ D * (2 * a + t) := by
    have := hnoise θhat
    rw [show dotProduct eps (X.mulVec (θhat - θstar)) = B from rfl,
        show dotProduct (X.mulVec (θhat - θstar)) (X.mulVec (θhat - θstar)) = D from rfl] at this
    convert this using 1
    simp only [ha_def]; ring


  suffices h : D ≤ 2 * b + t by
    have : 2 * b + t = 2 * ↑n * τ ^ 2 * ↑(l0norm θstar) + t := by
      simp only [hb_def]; ring
    linarith
  nlinarith [sq_nonneg (D - 2 * B)]







