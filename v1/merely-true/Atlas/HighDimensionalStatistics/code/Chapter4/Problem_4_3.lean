/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1
import Mathlib.Order.Bounds.Basic

open Matrix Real Finset MeasureTheory

noncomputable section

namespace Chapter4.Problem43

/-- Squared Frobenius norm of a `Fin d × Fin T` real matrix. -/
def frobSqNorm {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Nuclear norm computed from a given SVD: the sum of singular values. -/
def nuclearNorm {d T : ℕ} (S : SVD d T) : ℝ :=
  ∑ j : Fin S.r, S.σval j

/-- Soft thresholding: `(x - τ)_+`, the positive part of `x - τ`. -/
def softThreshold (x τ : ℝ) : ℝ := max (x - τ) 0

/-- Apply soft thresholding to the singular values of `S`, producing the soft-thresholded
matrix $\sum_j (\sigma_j - \tau)_+\, u_j v_j^\top$. -/
def softThreshMatrix {d T : ℕ} (S : SVD d T) (τ : ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, softThreshold (S.σval j) τ • vecMulVec (S.u j) (S.v j)

/-- `(M, S)` is a minimizer of the nuclear-norm penalized least squares problem
$\arg\min_M \|Y - M\|_F^2/n + \tau \|M\|_*$. -/
def IsNuclearNormMinimizer {d T : ℕ} (Y M : Matrix (Fin d) (Fin T) ℝ)
    (S : SVD d T) (τ : ℝ) (n : ℕ) : Prop :=
  S.IsDecompOf M ∧
  ∀ (M' : Matrix (Fin d) (Fin T) ℝ) (S' : SVD d T), S'.IsDecompOf M' →
    frobSqNorm (Y - M) / n + τ * nuclearNorm S ≤
      frobSqNorm (Y - M') / n + τ * nuclearNorm S'

/-- If `|x| ≤ y` then `x^2 ≤ y^2`. -/
theorem sq_le_of_abs_le {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith [sq_abs x, sq_abs y, abs_nonneg x]

/-- Oracle squared error: the midpoint $(\hat\sigma + \sigma^*)/2$ is within $\tau/2$ of
$\sigma^*$ whenever $|\hat\sigma - \sigma^*| \le \tau$. -/
theorem oracle_sv_error_sq (sigmaHat sigmaStar τ : ℝ)
    (hperturb : |sigmaHat - sigmaStar| ≤ τ) :
    ((sigmaHat + sigmaStar) / 2 - sigmaStar) ^ 2 ≤ τ ^ 2 / 4 := by
  have h1 : (sigmaHat + sigmaStar) / 2 - sigmaStar = (sigmaHat - sigmaStar) / 2 := by ring
  rw [h1]
  have h2 : ((sigmaHat - sigmaStar) / 2) ^ 2 = (sigmaHat - sigmaStar) ^ 2 / 4 := by ring
  rw [h2]
  linarith [sq_le_of_abs_le hperturb]

/-- **Problem 4.3, part 2** (closed form). With the oracle threshold
$t = (\hat\sigma - \sigma^*)/2$, soft thresholding `(\hat\sigma - t)_+` produces the
midpoint $(\hat\sigma + \sigma^*)/2$. -/
theorem problem_4_3_part2_closed_form
    (sigmaHat sigmaStar t : ℝ)
    (_hnn_hat : 0 ≤ sigmaHat) (hnn_star : 0 ≤ sigmaStar)
    (ht : t = (sigmaHat - sigmaStar) / 2) :
    max (sigmaHat - t) 0 = (sigmaHat + sigmaStar) / 2 := by
  rw [ht]
  have h : sigmaHat - (sigmaHat - sigmaStar) / 2 =
      (sigmaHat + sigmaStar) / 2 := by ring
  rw [h]; exact max_eq_left (by linarith)

end Chapter4.Problem43
end
