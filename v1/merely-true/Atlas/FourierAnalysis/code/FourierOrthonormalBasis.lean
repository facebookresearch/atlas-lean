/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MeasureTheory MeasureTheory.Measure AddCircle

namespace FourierOrthonormalBasis

variable {T : ℝ} [hT : Fact (0 < T)]

theorem fourier_hilbertBasis :
    ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT),
      ⇑b = @fourierLp T hT 2 _ :=
  ⟨fourierBasis, coe_fourierBasis⟩

end FourierOrthonormalBasis

end
