/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Finset BigOperators

namespace Rigollet

variable {n d : ℕ}

/-- Squared Euclidean norm of a vector `v ∈ ℝ^m`. -/
noncomputable def l2normSq {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- Ridge regression estimator with regularisation `τ`:
`θ̂_τ = (XᵀX + nτ I)⁻¹ Xᵀ Y`. -/
noncomputable def ridgeEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) : Fin d → ℝ :=
  (Xᵀ * X + (↑n * τ) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹.mulVec (Xᵀ.mulVec Y)

end Rigollet
