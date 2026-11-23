/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.CDF
import Mathlib.Topology.Algebra.Module.Cardinality

open MeasureTheory Filter ProbabilityTheory Set Function
open scoped Topology BoundedContinuousFunction ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

/-- If the CDF of a probability measure `μ` is continuous at `x`, then `μ` assigns zero mass to
the singleton `{x}`. Continuity of the CDF at `x` corresponds to absence of an atom at `x`. -/
lemma cdf_continuousAt_singleton_null
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (hx : ContinuousAt (cdf μ) x) :
    μ {x} = 0 := by
  rw [← measure_cdf (μ := μ), StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero]
  have : leftLim (↑(cdf μ)) x = (cdf μ) x := by
    have := (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mp hx
    rw [StieltjesFunction.rightLim_eq] at this
    exact this
  linarith

/-- If the CDF of a probability measure `μ` is continuous at `x`, then the boundary
`frontier (Iic x) = {x}` is `μ`-null. This is the form needed for the Portmanteau theorem. -/
lemma cdf_continuousAt_frontier_Iic_null
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (hx : ContinuousAt (cdf μ) x) :
    μ (frontier (Iic x)) = 0 := by
  rw [frontier_Iic]
  exact cdf_continuousAt_singleton_null μ x hx

/-- For a probability measure `ν` on `ℝ`, the mass of a half-open interval `(a, b]` equals
`F(b) - F(a)` (cast to `ℝ≥0`), where `F` is the CDF of `ν`. -/
lemma probMeasure_Ioc_eq_toNNReal_cdf (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    ν (Ioc a b) = (cdf (ν : Measure ℝ) b - cdf (ν : Measure ℝ) a).toNNReal := by
  show ((ν : Measure ℝ) (Ioc a b)).toNNReal = _
  conv_lhs => rw [← measure_cdf (μ := (ν : Measure ℝ))]
  rw [StieltjesFunction.measure_Ioc]
  exact NNReal.eq rfl

/-- The set of continuity points of the CDF of a probability measure is dense in `ℝ`. This
follows from the fact that a monotone function has only countably many discontinuities. -/
lemma dense_cdf_continuityPoints (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Dense {x : ℝ | ContinuousAt (cdf μ) x} := by
  have hcount : {x : ℝ | ¬ContinuousAt (↑(cdf μ)) x}.Countable :=
    (monotone_cdf μ).countable_not_continuousAt
  have hd := hcount.dense_compl (𝕜 := ℝ)
  rw [compl_setOf] at hd
  exact hd.mono fun x hx => not_not.mp hx

/-- **Portmanteau theorem** (weak convergence via bounded continuous functions). A sequence
of probability measures `μₙ` on `ℝ` converges weakly to `μ` if and only if
`∫ f dμₙ → ∫ f dμ` for every bounded continuous function `f : ℝ →ᵇ ℝ`. -/
theorem weakConvergence_iff_bounded_continuous
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ) :
    Tendsto μs atTop (𝓝 μ) ↔
      (∀ f : ℝ →ᵇ ℝ,
        Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure ℝ)) atTop
          (𝓝 (∫ x, f x ∂(μ : Measure ℝ)))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto

end ProbabilityTheory
