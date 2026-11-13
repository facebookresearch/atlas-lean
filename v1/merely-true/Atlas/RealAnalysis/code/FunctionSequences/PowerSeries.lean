/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Filter Topology

open scoped NNReal ENNReal

namespace FunctionSequences

/-- A real power series about a center point `x₀`, given by a sequence of real coefficients
`a : ℕ → ℝ`. Formally, it represents the formal series `∑ₘ aₘ (x - x₀)^m`. -/
structure PowerSeries where
  a : ℕ → ℝ
  x₀ : ℝ

/-- The `m`-th term of the power series `p` evaluated at `x`, i.e. `aₘ · (x - x₀)^m`. -/
def PowerSeries.term (p : PowerSeries) (x : ℝ) (m : ℕ) : ℝ :=
  p.a m * (x - p.x₀) ^ m

/-- The `n`-th partial sum of the power series `p` evaluated at `x`, i.e.
`∑_{m=0}^{n-1} aₘ (x - x₀)^m`. -/
def PowerSeries.partialSum (p : PowerSeries) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, p.term x m

/-- The radius of convergence `ρ` of a real power series with coefficients `a : ℕ → ℝ`,
defined via the Cauchy–Hadamard formula as the reciprocal of
`limsup_{n → ∞} ‖aₙ‖^(1/n)`, taking values in `ℝ≥0∞`. -/
noncomputable def radiusOfConvergence (a : ℕ → ℝ) : ENNReal :=
  (limsup (fun n => ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop)⁻¹

/-- The Cauchy–Hadamard radius of convergence of a scalar power series with coefficients `a`
agrees with the radius of the associated formal multilinear series
`FormalMultilinearSeries.ofScalars ℝ a` from Mathlib. -/
theorem radiusOfConvergence_eq_formalRadius (a : ℕ → ℝ) :
    radiusOfConvergence a = (FormalMultilinearSeries.ofScalars ℝ a).radius := by
  unfold radiusOfConvergence
  have heq : (fun n => ((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) =
      (fun n => ((‖FormalMultilinearSeries.ofScalars ℝ a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) := by
    ext n; congr 1; congr 1
    simp only [FormalMultilinearSeries.ofScalars, nnnorm_smul]
    have h : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ‖₊ = 1 := by
      ext; simp [ContinuousMultilinearMap.norm_mkPiAlgebraFin]
    rw [h, mul_one]
  rw [heq, ← FormalMultilinearSeries.radius_inv_eq_limsup]
  exact inv_inv _

/-- The absolute values of the terms of a summable real sequence are uniformly bounded:
if `f : ℕ → ℝ` is summable, then there exists a constant `C` with `|f n| ≤ C` for all `n`. -/
lemma summable_abs_bounded (f : ℕ → ℝ) (hf : Summable f) : ∃ C, ∀ n, |f n| ≤ C := by
  have htend := hf.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend 1 one_pos
  refine ⟨(∑ i ∈ Finset.range N, |f i|) + 1, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h1 := hN n hn
    rw [Real.dist_eq, sub_zero] at h1
    linarith [Finset.sum_nonneg (fun i _ => abs_nonneg (f i)) (s := Finset.range N)]
  · have hn' : n < N := not_le.mp hn
    calc |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn')
      _ ≤ (∑ i ∈ Finset.range N, |f i|) + 1 := le_add_of_nonneg_right one_pos.le

/-- Comparison criterion for the radius of convergence: if the sequence
`|aₙ| · rⁿ` is uniformly bounded by some constant `C`, then `r` lies inside the
disk of convergence, i.e. `r ≤ radiusOfConvergence a`. -/
theorem le_radiusOfConvergence_of_bound (a : ℕ → ℝ) (r : NNReal) (C : ℝ)
    (h : ∀ n, |a n| * (r : ℝ) ^ n ≤ C) :
    (r : ENNReal) ≤ radiusOfConvergence a := by
  rw [radiusOfConvergence_eq_formalRadius]
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  simp only [FormalMultilinearSeries.ofScalars, norm_smul,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, Real.norm_eq_abs]
  exact h n

/-- Absolute convergence inside the radius of convergence: for any `r < radiusOfConvergence a`,
the series `∑ₙ |aₙ| · rⁿ` is summable. -/
lemma summable_abs_mul_pow_of_lt_radius (a : ℕ → ℝ) (r : NNReal)
    (hr : (r : ENNReal) < radiusOfConvergence a) :
    Summable (fun n => |a n| * (r : ℝ) ^ n) := by
  rw [radiusOfConvergence_eq_formalRadius] at hr
  have h := (FormalMultilinearSeries.ofScalars ℝ a).summable_norm_mul_pow hr
  simp only [FormalMultilinearSeries.ofScalars, norm_smul,
    ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Uniform convergence of a power series on closed sub-intervals of its disk of convergence:
if `∑ aⱼ (x - x₀)^j` has radius of convergence `ρ ∈ (0, ∞]`, then for every `r ∈ (0, ρ)` the
partial sums converge uniformly on `[x₀ - r, x₀ + r]` to the sum `∑' j, aⱼ (x - x₀)^j`. -/
theorem power_series_uniform_convergence (a : ℕ → ℝ) (x₀ : ℝ) (r : ℝ) (hr : 0 < r)
    (hr_lt : ENNReal.ofReal r < radiusOfConvergence a) :
    TendstoUniformlyOn (fun n x => ∑ j ∈ Finset.range n, a j * (x - x₀) ^ j)
      (fun x => ∑' j, a j * (x - x₀) ^ j) Filter.atTop (Set.Icc (x₀ - r) (x₀ + r)) := by
  set rnn : NNReal := ⟨r, hr.le⟩
  have hrnn_lt : (rnn : ENNReal) < radiusOfConvergence a := by
    simp only [rnn, ENNReal.ofReal_eq_coe_nnreal hr.le] at hr_lt ⊢
    exact hr_lt
  have hsum : Summable (fun j => |a j| * r ^ j) :=
    summable_abs_mul_pow_of_lt_radius a rnn hrnn_lt
  have hbound : ∀ j, ∀ x ∈ Set.Icc (x₀ - r) (x₀ + r),
      ‖a j * (x - x₀) ^ j‖ ≤ |a j| * r ^ j := by
    intro j x hx
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    gcongr
    have hx_bound : |x - x₀| ≤ r := by
      rw [abs_le]
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    exact hx_bound
  exact tendstoUniformlyOn_tsum_nat hsum hbound

end FunctionSequences
