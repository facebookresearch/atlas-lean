/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Centering
import Atlas.TheoryOfProbability.code.Martingale

open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace DoobDecomposition

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {f : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}

/-- For a submartingale `f`, the predictable part `A_n` is almost-everywhere
nondecreasing: `A_n ≤ A_{n+1}` a.e. This uses that `E[f_{n+1} - f_n | ℱ n] ≥ 0` for a
submartingale. -/
theorem predictablePart_mono_of_submartingale
    (hf : Submartingale f ℱ μ) (n : ℕ) :
    predictablePart f ℱ μ n ≤ᵐ[μ] predictablePart f ℱ μ (n + 1) := by
  have key : (0 : Ω → ℝ) ≤ᵐ[μ] μ[f (n + 1) - f n | ℱ n] :=
    hf.condExp_sub_nonneg (Nat.le_succ n)
  filter_upwards [key] with ω hω
  simp only [predictablePart, Finset.sum_apply, Finset.sum_range_succ, Pi.zero_apply] at hω ⊢
  linarith

/-- **Doob's decomposition theorem.** Any submartingale `f` admits the decomposition
`f = M + A` where `M = martingalePart f ℱ μ` is a martingale and
`A = predictablePart f ℱ μ` is a predictable, almost-everywhere nondecreasing process
with `A 0 = 0`. -/
theorem doob_decomposition [SigmaFiniteFiltration μ ℱ]
    (hf : Submartingale f ℱ μ) :
    Martingale (martingalePart f ℱ μ) ℱ μ
    ∧ (predictablePart f ℱ μ 0 = 0)
    ∧ StronglyAdapted ℱ (fun n => predictablePart f ℱ μ (n + 1))
    ∧ (∀ n, predictablePart f ℱ μ n ≤ᵐ[μ] predictablePart f ℱ μ (n + 1))
    ∧ (martingalePart f ℱ μ + predictablePart f ℱ μ = f) :=
  ⟨martingale_martingalePart hf.stronglyAdapted hf.integrable,
   predictablePart_zero,
   stronglyAdapted_predictablePart,
   fun n => predictablePart_mono_of_submartingale hf n,
   martingalePart_add_predictablePart ℱ μ f⟩

end DoobDecomposition
