/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.LinnikLargeSieve

open Finset Complex

noncomputable section

namespace LinnikLargeSieve



/-- Average over primes `p ∈ P_M` of the squared $L^2$ norm of the high-frequency part of the
mod-`p` projection: `Avg_{p ∈ P_M} ‖(π_p f)_H‖_{L^2}^2 = (1/|P_M|) · linnikLHS N M f`. -/
def avgProjHighFreqL2Sq (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  (1 / ((primesInRange M).card : ℝ)) * linnikLHS N M f


end LinnikLargeSieve

end
