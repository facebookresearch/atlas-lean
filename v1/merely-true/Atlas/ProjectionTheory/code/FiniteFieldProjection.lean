/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic

namespace FiniteFieldProjection

open Finset

/-- Projection of a point `x = (x₁, x₂) ∈ 𝔽_p²` onto the direction `θ`:
`π_θ(x) = x₁ + θ · x₂`. -/
def piTheta {p : ℕ} (θ : ZMod p) : ZMod p × ZMod p → ZMod p :=
  fun x => x.1 + θ * x.2



end FiniteFieldProjection
