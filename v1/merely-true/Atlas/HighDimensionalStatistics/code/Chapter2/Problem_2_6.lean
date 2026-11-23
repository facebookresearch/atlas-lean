/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Mathlib

open Finset Matrix BigOperators Rigollet

/-- Modified BIC objective: data fit plus a log-adjusted sparsity penalty,
`(1/n) · ‖Y - Xθ‖² + λ · ‖θ‖_0 · log(e·d / ‖θ‖_0)`. -/
noncomputable def modifiedBICObjective {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (lam : ℝ) (θ : Fin d → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ‖Y - X.mulVec θ‖^2 +
    lam * (l0norm θ : ℝ) * Real.log (Real.exp 1 * ↑d / (l0norm θ : ℝ))

/-- `θ̂` is a modified-BIC estimator if it minimises `modifiedBICObjective`. -/
def IsModifiedBICEstimator {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (lam : ℝ) (θhat : Fin d → ℝ) : Prop :=
  ∀ θ : Fin d → ℝ, modifiedBICObjective X Y lam θhat ≤ modifiedBICObjective X Y lam θ
