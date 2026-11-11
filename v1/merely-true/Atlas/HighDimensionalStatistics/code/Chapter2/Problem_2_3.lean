/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open BigOperators

namespace Rigollet

variable {d : ℕ}

/-- Hard thresholding operator at level `2τ`: keeps coordinates with `|y_j| > 2τ`,
zeroing out the rest. -/
noncomputable def hardThresh (τ : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if |y j| > 2 * τ then y j else 0

end Rigollet
