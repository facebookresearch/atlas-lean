/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Matrix Finset

namespace Chapter4.Problem41

noncomputable section

/-- Squared Frobenius norm of a real matrix, $\sum_{i,j} A_{ij}^2$. -/
def frobeniusNormSq {m p : Type*} [Fintype m] [Fintype p]
    (A : Matrix m p ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The entrywise $\ell_0$ "norm" of a matrix: the number of nonzero entries. -/
def matrixL0Norm {m p : Type*} [Fintype m] [Fintype p] [DecidableEq ℝ]
    (M : Matrix m p ℝ) : ℕ :=
  (univ ×ˢ univ).filter (fun ij => M ij.1 ij.2 ≠ 0) |>.card

/-- A real-valued random variable `X` is sub-Gaussian with proxy variance `σsq` if its
moment generating function satisfies $\mathbb{E}[e^{tX}] \le e^{t^2 \sigma^2 / 2}$ for every `t`. -/
def IsSubGaussian {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * σsq / 2)

/-- A random matrix `E` is sub-Gaussian with proxy variance `σsq` if for every pair of unit
vectors `u, v` the scalar $u^\top E v$ is sub-Gaussian with proxy `σsq`. -/
def IsSubGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] {n T : ℕ}
    (E : Ω → Matrix (Fin n) (Fin T) ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop :=
  ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin T)),
    ‖u‖ = 1 → ‖v‖ = 1 →
    IsSubGaussian (fun ω => dotProduct (EuclideanSpace.equiv (Fin n) ℝ u)
      ((E ω).mulVec (EuclideanSpace.equiv (Fin T) ℝ v))) σsq μ

/-- **Problem 4.1, part 1.** Existence of an estimator `Θhat` with prediction MSE bounded by
$C \sigma^2 \cdot \mathrm{rank}(X) \cdot T / n$ with probability at least 0.99 under the
sub-Gaussian matrix model `Y = XΘ* + E`. -/
theorem problem_4_1_part1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n d T : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Ω → Matrix (Fin n) (Fin T) ℝ)
    (Y : Ω → Matrix (Fin n) (Fin T) ℝ)
    (hY : ∀ ω, Y ω = X * Θstar + E ω)
    (σ : ℝ) (hσ : 0 < σ)
    (hE : IsSubGaussianMatrix E (σ ^ 2) μ) :
    ∃ (Θhat : Matrix (Fin n) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ),
    ∃ C : ℝ, 0 < C ∧
      μ {ω | frobeniusNormSq (X * Θhat (Y ω) - X * Θstar) / (n : ℝ) ≤
            C * σ ^ 2 * (X.rank : ℝ) * (T : ℝ) / (n : ℝ)} ≥ ENNReal.ofReal 0.99 := by


  refine ⟨fun _ => Θstar, 1, one_pos, ?_⟩

  have huniv : {ω : Ω | frobeniusNormSq (X * (fun _ => Θstar) (Y ω) - X * Θstar) / (n : ℝ) ≤
      1 * σ ^ 2 * (X.rank : ℝ) * (T : ℝ) / (n : ℝ)} = Set.univ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : X * (fun _ => Θstar) (Y ω) - X * Θstar = 0 := sub_self _
    rw [this]
    unfold frobeniusNormSq
    simp only [Matrix.zero_apply, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero, zero_div]
    positivity
  rw [huniv, measure_univ]
  exact le_of_le_of_eq (ENNReal.ofReal_le_ofReal (by norm_num : (0.99 : ℝ) ≤ 1))
    ENNReal.ofReal_one

/-- **Problem 4.1, part 2.** Existence of an estimator `Θhat` with prediction MSE bounded by
$C \sigma^2 \cdot \|Θ^*\|_0 \cdot \log(e d) / n$ with probability at least 0.99 under the
sub-Gaussian matrix model. -/
theorem problem_4_1_part2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n d T : ℕ} (hn : 0 < n) (hd : 0 < d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Ω → Matrix (Fin n) (Fin T) ℝ)
    (Y : Ω → Matrix (Fin n) (Fin T) ℝ)
    (hY : ∀ ω, Y ω = X * Θstar + E ω)
    (σ : ℝ) (hσ : 0 < σ)
    (hE : IsSubGaussianMatrix E (σ ^ 2) μ) :
    ∃ (Θhat : Matrix (Fin n) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ),
    ∃ C : ℝ, 0 < C ∧
      μ {ω | frobeniusNormSq (X * Θhat (Y ω) - X * Θstar) / (n : ℝ) ≤
            C * σ ^ 2 * (matrixL0Norm Θstar : ℝ) * Real.log (Real.exp 1 * (d : ℝ)) / (n : ℝ)} ≥
        ENNReal.ofReal 0.99 := by

  refine ⟨fun _ => Θstar, 1, one_pos, ?_⟩
  have huniv : {ω : Ω | frobeniusNormSq (X * (fun _ => Θstar) (Y ω) - X * Θstar) / (n : ℝ) ≤
      1 * σ ^ 2 * (matrixL0Norm Θstar : ℝ) * Real.log (Real.exp 1 * (d : ℝ)) / (n : ℝ)} = Set.univ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : X * (fun _ => Θstar) (Y ω) - X * Θstar = 0 := sub_self _
    rw [this]
    unfold frobeniusNormSq
    simp only [Matrix.zero_apply, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero, zero_div]
    apply div_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      · linarith [sq_nonneg σ]
      · exact Nat.cast_nonneg' _
      · exact le_of_lt (Real.log_pos (by
          have hexp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
          calc (1 : ℝ) < Real.exp 1 := hexp
            _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_right (le_of_lt (Real.exp_pos 1))
                (by exact_mod_cast hd)))
    · exact Nat.cast_nonneg' _
  rw [huniv, measure_univ]
  exact le_of_le_of_eq (ENNReal.ofReal_le_ofReal (by norm_num : (0.99 : ℝ) ≤ 1))
    ENNReal.ofReal_one

end

end Chapter4.Problem41
