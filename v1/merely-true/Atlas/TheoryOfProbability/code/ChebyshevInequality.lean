/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.Variance
import Atlas.TheoryOfProbability.code.MarkovInequality

open MeasureTheory ProbabilityTheory

/-- **Chebyshev's inequality.** If `X` has finite mean and variance, then for any
`a > 0`,
`P{|X − E[X]| ≥ a} ≤ Var(X) / a²`.
The result is derived from Markov's inequality applied to `(X − E[X])²`. -/
theorem chebyshev_inequality {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ |X ω - μ[X]|} ≤ Var[X; μ] / a ^ 2 := by

  have hY_nn : 0 ≤ᵐ[μ] (fun ω => (X ω - μ[X]) ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hY_int : Integrable (fun ω => (X ω - μ[X]) ^ 2) μ :=
    (hX.sub (memLp_const _)).integrable_sq
  have ha2 : (0 : ℝ) < a ^ 2 := sq_pos_of_pos ha

  have markov := markov_inequality hY_nn hY_int ha2


  have hset : {ω | a ^ 2 ≤ (X ω - μ[X]) ^ 2} = {ω | a ≤ |X ω - μ[X]|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [sq_le_sq, abs_of_pos ha]
  rw [hset] at markov

  have hvar : (∫ ω, (X ω - μ[X]) ^ 2 ∂μ) = Var[X; μ] :=
    (variance_eq_integral hX.1.aemeasurable).symm
  rw [hvar] at markov
  exact markov
