/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace MonotoneConvergence

open MeasureTheory Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Monotone Convergence Theorem (Beppo Levi) restricted to a measurable set:
for a pointwise nondecreasing sequence of measurable `ℝ≥0∞`-valued functions, the
pointwise supremum is measurable, the integral of the supremum equals the supremum
of the integrals over `E`, and the sequence of integrals converges to that value. -/
theorem monotone_convergence_theorem'
    {f : ℕ → α → ENNReal} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f)
    {E : Set α} (_hE : MeasurableSet E) :
    Measurable (fun x => ⨆ n, f n x) ∧
    (∫⁻ x in E, (⨆ n, f n x) ∂μ = ⨆ n, ∫⁻ x in E, f n x ∂μ) ∧
    Tendsto (fun n => ∫⁻ x in E, f n x ∂μ) atTop
      (𝓝 (∫⁻ x in E, (⨆ n, f n x) ∂μ)) := by
  refine ⟨Measurable.iSup hf, lintegral_iSup hf h_mono, ?_⟩
  rw [lintegral_iSup hf h_mono]
  apply tendsto_atTop_iSup
  intro i j hij
  exact lintegral_mono (h_mono hij)

end MonotoneConvergence
