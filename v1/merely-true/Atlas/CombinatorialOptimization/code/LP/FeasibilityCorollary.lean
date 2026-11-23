/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.LP.WeakDualityStandard

open Matrix

theorem feasibility_corollary_primal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (hy : ∀ j, c j ≤ (Aᵀ *ᵥ y) j) :
    ∀ x : Fin n → ℝ, (A *ᵥ x = b) → (∀ j, 0 ≤ x j) → dotProduct c x ≤ dotProduct b y :=
  fun x hAx hx => weak_duality_standard A b c x y hAx hx hy
