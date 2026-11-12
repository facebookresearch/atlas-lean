/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

noncomputable section

open MeasureTheory Filter Complex
open scoped FourierTransform RealInnerProductSpace Topology

namespace FourierL1BoundedC0

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier transform is bounded `L¹ → L∞`: for any integrable function `f`, the
pointwise norm of `𝓕 f` is dominated by the `L¹` norm of `f`. -/
theorem fourier_norm_le_L1_norm (f : V → E) (w : V) :
    ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ f w

/-- Riemann–Lebesgue lemma: the Fourier transform of an `L¹` function tends to zero at
infinity, so `𝓕 : L¹(V) → C₀(V)` is well-defined. -/
theorem fourier_tendsto_zero_at_infty (f : V → E) :
    Tendsto (𝓕 f) (cocompact V) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f

end FourierL1BoundedC0

end
