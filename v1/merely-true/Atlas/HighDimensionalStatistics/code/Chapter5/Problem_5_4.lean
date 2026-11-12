/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13

open MeasureTheory Cor_5_13

noncomputable section

namespace Problem_5_4

/-- Euclidean ball of squared radius `r` in `ℝ^d` (under `sqDist`). -/
def euclideanBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) :=
  {θ | sqDist θ 0 ≤ r}

/-- Unit `ℓ∞`-ball `{θ ∈ ℝ^d : max_i |θ i| ≤ 1}`. -/
def linfBall (d : ℕ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, |θ i| ≤ 1}

/-- Non-negative orthant `{θ ∈ ℝ^d : θ_i ≥ 0 for all i}`. -/
def nonnegOrthant (d : ℕ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, 0 ≤ θ i}

/-- Scaled binary hypercube `{0, c}^d ⊂ ℝ^d`. -/
def scaledHypercube (d : ℕ) (c : ℝ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, θ i = 0 ∨ θ i = c}





end Problem_5_4

end
