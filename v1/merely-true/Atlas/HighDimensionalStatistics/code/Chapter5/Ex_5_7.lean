/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GaussianKL

/-- Squared Euclidean distance `∑ i, (θ₁ i - θ₂ i)²` on `Fin d → ℝ`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- KL divergence between two univariate Gaussians with common variance `v`:
`KL(N(θ₁, v) ‖ N(θ₂, v)) = (θ₁ - θ₂)² / (2v)` (Example 5.7). -/
def klDiv_gaussian (θ₁ θ₂ : ℝ) (v : ℝ) : ℝ :=
  (θ₁ - θ₂) ^ 2 / (2 * v)

/-- Multidimensional generalisation of `klDiv_gaussian`: KL divergence between
two isotropic Gaussians with common variance `v` equals `‖θ₁ - θ₂‖² / (2v)`. -/
def klDiv_gaussian_d {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) (v : ℝ) : ℝ :=
  sqDist θ₁ θ₂ / (2 * v)

end GaussianKL
