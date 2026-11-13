/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Chapter4

open Matrix Finset

/-- Squared Frobenius norm of a real matrix, $\sum_{i,j} A_{ij}^2$. -/
noncomputable def frobeniusNormSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, (A i j) ^ 2

/-- The squared Frobenius norm is nonnegative. -/
theorem frobeniusNormSq_nonneg {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) :
    0 ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The squared Frobenius norm of the zero matrix is zero. -/
theorem frobeniusNormSq_zero {m p : ℕ} :
    frobeniusNormSq (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
  unfold frobeniusNormSq
  simp [Matrix.zero_apply, sq]

/-- Operator (spectral) norm of a rectangular real matrix. -/
noncomputable def rectOpNorm {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin (𝕜 := ℝ) A).toContinuousLinearMap‖

/-- The operator norm of the zero matrix vanishes. -/
lemma rectOpNorm_zero (m p : ℕ) : rectOpNorm (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
  simp [rectOpNorm, map_zero]

/-- Dual definition of the nuclear norm: $\|A\|_* = \sup_{\|B\|_{op} \le 1} \langle B, A\rangle_F$. -/
noncomputable def nuclearNorm {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  sSup { t : ℝ | ∃ B : Matrix (Fin d) (Fin T) ℝ, rectOpNorm B ≤ 1 ∧
    t = ∑ i, ∑ j, B i j * A i j }

/-- The nuclear norm is nonnegative. -/
theorem nuclearNorm_nonneg {d T : ℕ} (Θ : Matrix (Fin d) (Fin T) ℝ) : 0 ≤ nuclearNorm Θ := by
  unfold nuclearNorm
  by_cases h : BddAbove { t : ℝ | ∃ B : Matrix (Fin d) (Fin T) ℝ, rectOpNorm B ≤ 1 ∧
    t = ∑ i, ∑ j, B i j * Θ i j }
  · apply le_csSup_of_le h
    · show ∃ B : Matrix (Fin d) (Fin T) ℝ, rectOpNorm B ≤ 1 ∧
        (0 : ℝ) = ∑ i, ∑ j, B i j * Θ i j
      exact ⟨0, by rw [rectOpNorm_zero]; exact zero_le_one, by simp⟩
    · exact le_refl 0
  · simp [csSup_of_not_bddAbove h, Real.sSup_empty]

/-- `s` is the largest singular value of `X` (i.e. its operator norm). -/
def IsLargestSingularValue {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℝ) : Prop :=
  s = ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖

/-- `s` is a positive singular value of `X` not exceeding its largest singular value
(used here as a weak surrogate for "smallest positive singular value"). -/
def IsSmallestPosSingularValue {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℝ) : Prop :=
  0 < s ∧ s ≤ ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖

/-- Nuclear-norm penalized least-squares objective:
$\frac{1}{n} \|Y - X\Theta\|_F^2 + \tau \|\Theta\|_*$. -/
noncomputable def nuclearNormObjective {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θ : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (Y - X * Θ) + τ * nuclearNorm Θ

/-- `Θhat` is a nuclear-norm penalized estimator if it minimizes `nuclearNormObjective`. -/
def IsNuclearNormEstimator {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θhat : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d) (Fin T) ℝ,
    nuclearNormObjective Y X τ Θhat ≤ nuclearNormObjective Y X τ Θ

/-- Prediction mean squared error: $\frac{1}{n} \|X\hat\Theta - X\Theta^*\|_F^2$. -/
noncomputable def predictionMSE {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (X * Θhat - X * Θstar)

end Chapter4
