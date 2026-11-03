/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

theorem weak_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hAx : A *ᵥ x ≤ b) (hx : 0 ≤ x)
    (hATy : Aᵀ *ᵥ y ≥ c) (hy : 0 ≤ y) :
    dotProduct c x ≤ dotProduct b y := by
  calc dotProduct c x
      ≤ dotProduct (Aᵀ *ᵥ y) x := dotProduct_le_dotProduct_of_nonneg_right hATy hx
    _ = dotProduct y (A *ᵥ x) := by
        rw [dotProduct_comm (Aᵀ *ᵥ y) x, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
            dotProduct_comm]
    _ ≤ dotProduct y b := dotProduct_le_dotProduct_of_nonneg_left hAx hy
    _ = dotProduct b y := dotProduct_comm y b
