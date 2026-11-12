/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Mathlib

open MeasureTheory Matrix Real Finset

namespace Rigollet.Chapter4.Thm_4_4

noncomputable section

/-- Squared Frobenius norm, $\sum_{i,j} A_{ij}^2$. -/
def frobeniusNormSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
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

/-- Frobenius (entrywise) inner product of two matrices. -/
def frobeniusInner {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, A i j * B i j

/-- Rank-penalized least-squares objective:
$\frac{1}{n}\|Y - X\Theta\|_F^2 + 2\tau^2 \cdot \mathrm{rank}(\Theta)$. -/
def rankPenObjective {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θ : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (Y - X * Θ) + 2 * τ ^ 2 * (Θ.rank : ℝ)

/-- `Θhat` is a rank-penalized estimator if it minimizes `rankPenObjective`. -/
def IsRankPenalizationEstimator {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θhat : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d) (Fin T) ℝ,
    rankPenObjective Y X τ Θhat ≤ rankPenObjective Y X τ Θ

/-- Prediction MSE: $\frac{1}{n}\|X\hat\Theta - X\Theta^*\|_F^2$. -/
def predictionMSE {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (X * Θhat - X * Θstar)

/-- Polarization-style expansion of the squared Frobenius norm of a difference. -/
theorem frobeniusNormSq_sub_eq {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    frobeniusNormSq (A - B) =
      frobeniusNormSq A + frobeniusNormSq B -
        2 * ∑ i : Fin m, ∑ j : Fin p, A i j * B i j := by
  unfold frobeniusNormSq
  simp only [Matrix.sub_apply]
  have h1 : ∀ i : Fin m, ∑ j : Fin p, (A i j - B i j) ^ 2 =
      (∑ j, A i j ^ 2) + (∑ j, B i j ^ 2) - 2 * (∑ j, A i j * B i j) := by
    intro i
    have : ∀ j, (A i j - B i j) ^ 2 =
        A i j ^ 2 + B i j ^ 2 - 2 * (A i j * B i j) := by intro j; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Adjoint identity for the Frobenius inner product:
$\langle E, X A\rangle_F = \langle X^\top E, A\rangle_F$. -/
theorem frobeniusInner_transpose_mul {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (E : Matrix (Fin n) (Fin T) ℝ)
    (A : Matrix (Fin d) (Fin T) ℝ) :
    frobeniusInner E (X * A) = frobeniusInner (Xᵀ * E) A := by
  simp only [frobeniusInner, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [show ∀ (i : Fin n) (j : Fin T) (k : Fin d),
    E i j * (X i k * A k j) = X i k * E i j * A k j from fun i j k => by ring]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.sum_comm]

/-- The rank of a difference is bounded by the sum of the ranks. -/
theorem rank_sub_le {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    (A - B).rank ≤ A.rank + B.rank := by
  have hneg : (-B).rank = B.rank := by
    unfold Matrix.rank
    have h : (-B).mulVecLin = -B.mulVecLin := by ext v; simp
    rw [show (-B).mulVecLin.range = B.mulVecLin.range from by rw [h, LinearMap.range_neg]]
  rw [sub_eq_add_neg]
  calc (A + (-B)).rank
      ≤ A.rank + (-B).rank := by
        unfold Matrix.rank
        have h_range : (A + (-B)).mulVecLin.range ≤
            A.mulVecLin.range ⊔ (-B).mulVecLin.range := by
          intro x hx
          rw [LinearMap.mem_range] at hx
          obtain ⟨v, hv⟩ := hx
          rw [Submodule.mem_sup]
          exact ⟨A.mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩,
                 (-B).mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩, by simp [← hv]⟩
        exact (Submodule.finrank_mono h_range).trans
          (Submodule.finrank_add_le_finrank_add_finrank _ _)
    _ = A.rank + B.rank := by rw [hneg]

/-- The rank of $X(\hat\Theta - \Theta^*)$ is bounded by $\mathrm{rank}(\hat\Theta) +
\mathrm{rank}(\Theta^*)$. -/
theorem rank_mul_sub_le_add {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) :
    (X * (Θhat - Θstar)).rank ≤ Θhat.rank + Θstar.rank :=
  (Matrix.rank_mul_le_right X _).trans (rank_sub_le _ _)

/-- The Frobenius inner product is homogeneous in its second argument. -/
lemma frobeniusInner_smul_right {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) (c : ℝ) :
    frobeniusInner A (c • B) = c * frobeniusInner A B := by
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ (i : Fin m) (j : Fin p),
    A i j * (c * B i j) = c * (A i j * B i j) from fun i j => by ring]
  simp_rw [← Finset.mul_sum]

/-- $\langle A, A\rangle_F = \|A\|_F^2$. -/
lemma frobeniusInner_self {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) :
    frobeniusInner A A = frobeniusNormSq A := by
  simp only [frobeniusInner, frobeniusNormSq]; congr 1; ext i; congr 1; ext j; ring

/-- A matrix with zero squared Frobenius norm has all entries equal to zero. -/
lemma entries_zero_of_frobeniusNormSq_zero {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ) (hB : frobeniusNormSq B = 0) :
    ∀ i j, B i j = 0 := by
  intro i j
  have h1 : ∀ x ∈ Finset.univ, (0 : ℝ) ≤ ∑ x_1, (B x x_1) ^ 2 :=
    fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  rw [frobeniusNormSq, Finset.sum_eq_zero_iff_of_nonneg h1] at hB
  have h2 : ∑ x_1, (B i x_1) ^ 2 = 0 := hB i (Finset.mem_univ _)
  have h3 : ∀ y ∈ Finset.univ, (0 : ℝ) ≤ (B i y) ^ 2 := fun y _ => sq_nonneg _
  rw [Finset.sum_eq_zero_iff_of_nonneg h3] at h2
  have h4 := h2 j (Finset.mem_univ _)
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h4

/-- If `B` has zero Frobenius norm then any inner product with it vanishes. -/
lemma frobeniusInner_zero_of_frobeniusNormSq_zero {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) (hB : frobeniusNormSq B = 0) :
    frobeniusInner A B = 0 := by
  have hB_zero := entries_zero_of_frobeniusNormSq_zero B hB
  simp only [frobeniusInner]
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  simp [hB_zero i j]

/-- Left-multiplication by an orthonormal `Φ` (i.e. $\Phi^\top \Phi = I$) preserves the
squared Frobenius norm. -/
lemma frobeniusNormSq_orth_left {n r T : ℕ} (Φ : Matrix (Fin n) (Fin r) ℝ) (hΦ : Φᵀ * Φ = 1)
    (C : Matrix (Fin r) (Fin T) ℝ) :
    frobeniusNormSq (Φ * C) = frobeniusNormSq C := by
  rw [← frobeniusInner_self, ← frobeniusInner_self]
  have h1 := frobeniusInner_transpose_mul Φ (Φ * C) C
  rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul] at h1
  exact h1


/-- Left-multiplying by `Φ` with $\Phi^\top \Phi = I$ does not decrease rank. -/
lemma rank_le_of_left_inverse_mul {n r T : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ) (hΦ : Φᵀ * Φ = 1)
    (C : Matrix (Fin r) (Fin T) ℝ) :
    C.rank ≤ (Φ * C).rank := by
  have h : C = Φᵀ * (Φ * C) := by rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  calc C.rank = (Φᵀ * (Φ * C)).rank := by rw [← h]
    _ ≤ (Φ * C).rank := Matrix.rank_mul_le_right Φᵀ (Φ * C)





/-- Substituting the true parameter `Θstar` into the minimizer inequality `hRK` produces the
basic inequality used in the analysis of the rank-penalized estimator. -/
theorem minimizer_substituted {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Y : Matrix (Fin n) (Fin T) ℝ)
    (hY : Y = X * Θstar + E)
    (τ : ℝ)
    (Θhat : Matrix (Fin d) (Fin T) ℝ)
    (hRK : IsRankPenalizationEstimator Y X τ Θhat) :
    (1 / (n : ℝ)) * frobeniusNormSq (E - (X * Θhat - X * Θstar)) +
      2 * τ ^ 2 * (Θhat.rank : ℝ) ≤
    (1 / (n : ℝ)) * frobeniusNormSq E + 2 * τ ^ 2 * (Θstar.rank : ℝ) := by
  have hmin := hRK Θstar
  unfold rankPenObjective at hmin

  have h1 : Y - X * Θhat = E - (X * Θhat - X * Θstar) := by
    rw [hY]; abel

  have h2 : Y - X * Θstar = E := by
    rw [hY]; abel
  rw [h1, h2] at hmin
  exact hmin


/-- Rate translation: with the canonical choice of threshold $\tau_0$, the rank-penalized
prediction MSE bound is at most $256 \log 12 \cdot \sigma_0 \cdot r \cdot (D + L)$. -/
theorem theorem_4_4_rate_bound
    (σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀)
    (D : ℝ) (hD : 0 ≤ D)
    (L : ℝ) (hL : 0 ≤ L)
    (r : ℝ) (hr : 0 ≤ r) :
    let τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) +
              2 * Real.sqrt σ₀ * Real.sqrt (2 * L)
    8 * r * τ₀ ^ 2 ≤ 256 * Real.log 12 * σ₀ * r * (D + L) := by
  set τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) +
            2 * Real.sqrt σ₀ * Real.sqrt (2 * L)
  set a := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) with ha_def
  set b := 2 * Real.sqrt σ₀ * Real.sqrt (2 * L) with hb_def
  have hlog12 : (0 : ℝ) ≤ Real.log 12 := (Real.log_pos (by norm_num : (1:ℝ) < 12)).le
  have ha_nn : 0 ≤ a := by positivity
  have hb_nn : 0 ≤ b := by positivity

  have hab_sq : τ₀ ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h : τ₀ = a + b := rfl
    nlinarith [sq_nonneg (a - b)]

  have ha_sq : a ^ 2 = 16 * σ₀ * (Real.log 12 * D) := by
    rw [ha_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
        Real.sq_sqrt (mul_nonneg hlog12 hD)]
    ring

  have hb_sq : b ^ 2 = 8 * σ₀ * L := by
    rw [hb_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
        Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL)]
    ring


  have hlog12_half : (1 : ℝ) / 2 ≤ Real.log 12 := by
    have h1 : Real.log 2 ≤ Real.log 12 :=
      Real.log_le_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 12)
    linarith [Real.log_two_gt_d9]
  calc 8 * r * τ₀ ^ 2
      ≤ 8 * r * (2 * (a ^ 2 + b ^ 2)) :=
        mul_le_mul_of_nonneg_left hab_sq (by positivity)
    _ = 8 * r * (2 * (16 * σ₀ * (Real.log 12 * D) + 8 * σ₀ * L)) := by
        rw [ha_sq, hb_sq]
    _ = 256 * Real.log 12 * σ₀ * r * D + 128 * σ₀ * r * L := by ring
    _ ≤ 256 * Real.log 12 * σ₀ * r * D + 256 * Real.log 12 * σ₀ * r * L := by
        have hσrL : 0 ≤ σ₀ * r * L := by positivity
        have : 128 * σ₀ * r * L ≤ 256 * Real.log 12 * σ₀ * r * L := by
          have h : (128 : ℝ) ≤ 256 * Real.log 12 := by nlinarith [hlog12_half]
          calc 128 * σ₀ * r * L = 128 * (σ₀ * r * L) := by ring
            _ ≤ (256 * Real.log 12) * (σ₀ * r * L) :=
                mul_le_mul_of_nonneg_right h hσrL
            _ = 256 * Real.log 12 * σ₀ * r * L := by ring
        linarith
    _ = 256 * Real.log 12 * σ₀ * r * (D + L) := by ring


end

end Rigollet.Chapter4.Thm_4_4
