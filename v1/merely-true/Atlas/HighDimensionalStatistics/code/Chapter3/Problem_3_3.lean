/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1

open Matrix Finset

namespace Chapter3

/-- Weak `ℓ_q` quasi-norm of a finite-dimensional vector `θ`:
`‖θ‖_{q,∞} = sup_{t > 0} t · #{i : |θᵢ| ≥ t}^{1/q}`. -/
noncomputable def weakLqNorm {M : ℕ} (q : ℝ) (θ : Fin M → ℝ) : ℝ :=
  ⨆ (t : ℝ) (_ : 0 < t),
    t * ((Finset.univ.filter (fun i => t ≤ |θ i|)).card : ℝ) ^ (1 / q)

end Chapter3
