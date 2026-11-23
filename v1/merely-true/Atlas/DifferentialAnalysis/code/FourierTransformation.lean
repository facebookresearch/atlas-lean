/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.LpSpace

noncomputable section

open scoped FourierTransform ComplexInnerProductSpace
open MeasureTheory SchwartzMap

namespace FourierTransformation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The Fourier transform restricts to a continuous `ℂ`-linear self-map of Schwartz
space: there exists `T : 𝓢(V, F) →L[ℂ] 𝓢(V, F)` whose underlying function agrees
with `𝓕` on every Schwartz function. -/
theorem fourier_continuousLinearMap :
    ∃ T : 𝓢(V, F) →L[ℂ] 𝓢(V, F), ∀ f : 𝓢(V, F), T f = 𝓕 f :=
  ⟨SchwartzMap.fourierTransformCLM ℂ, fun _ => rfl⟩

variable [CompleteSpace F]

end FourierTransformation

end
