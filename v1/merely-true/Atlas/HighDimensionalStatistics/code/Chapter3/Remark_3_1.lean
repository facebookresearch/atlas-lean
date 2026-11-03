/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Chapter3

/-- Empirical mean squared error between predictions `fhat` and the truth
`f`: `(1/n) ∑ᵢ (fhatᵢ - fᵢ)²`. -/
noncomputable def MSE {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

/-- Number of non-zero coordinates of a vector (the `ℓ₀` "norm"). -/
noncomputable def support_size {M : ℕ} (θ : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- `ℓ₁` norm `‖θ‖₁ = ∑ᵢ |θᵢ|`. -/
noncomputable def l1norm {M : ℕ} (θ : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, |θ i|

/-- Least-squares objective `(1/n) ‖Y - Φ θ‖²`. -/
noncomputable def lsObjective {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (θ : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (Y i - (Φ.mulVec θ) i) ^ 2

/-- BIC penalized objective: least-squares loss plus `τ²` times the size
of the support of `θ`. -/
noncomputable def bicObjective {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (τ : ℝ) (θ : Fin M → ℝ) : ℝ :=
  lsObjective Y Φ θ + τ ^ 2 * (support_size θ : ℝ)

/-- LASSO objective: least-squares loss plus `2τ‖θ‖₁`. -/
noncomputable def lassoObjective {n M : ℕ} (Y : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin M) ℝ)
    (τ : ℝ) (θ : Fin M → ℝ) : ℝ :=
  lsObjective Y Φ θ + 2 * τ * l1norm θ

/-- The empirical MSE is always non-negative. -/
theorem MSE_nonneg {n : ℕ} (fhat f : Fin n → ℝ) : 0 ≤ MSE fhat f := by
  unfold MSE
  apply mul_nonneg
  · apply div_nonneg zero_le_one (Nat.cast_nonneg n)
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Chapter3
