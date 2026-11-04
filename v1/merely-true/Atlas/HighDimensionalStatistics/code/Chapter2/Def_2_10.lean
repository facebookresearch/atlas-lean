/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

variable {d : ℕ}

/-- **Definition 2.10 (Hard thresholding estimator)**: keeps each coordinate `y_j`
whose magnitude exceeds the threshold `2τ`, and sets the others to zero. -/
noncomputable def hardThreshold (τ : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if |y j| > 2 * τ then y j else 0

/-- Soft thresholding estimator at level `2τ`: shrinks each coordinate towards zero
by `2τ`, and zeros out those with `|y_j| ≤ 2τ`. -/
noncomputable def softThreshold (τ : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if y j > 2 * τ then y j - 2 * τ
            else if y j < -(2 * τ) then y j + 2 * τ
            else 0
