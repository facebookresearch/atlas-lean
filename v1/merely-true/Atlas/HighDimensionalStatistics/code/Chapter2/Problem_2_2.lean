/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Matrix BigOperators

namespace Rigollet

/-- Vandermonde feature vector `(1, z, z², …, z^{d-1})` associated to a real scalar `z`. -/
noncomputable def vandermondeVec (d : ℕ) (z : ℝ) : Fin d → ℝ :=
  fun i => z ^ (i : ℕ)

/-- Moment matrix of `μ` in the Vandermonde basis: entry `(i, j)` is `∫ z^{i+j} dμ`. -/
noncomputable def vandermondeMomentMatrix (d : ℕ) (μ : Measure ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ z, z ^ ((i : ℕ) + (j : ℕ)) ∂μ

end Rigollet
