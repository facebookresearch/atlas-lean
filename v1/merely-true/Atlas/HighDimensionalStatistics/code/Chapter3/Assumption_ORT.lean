/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

namespace OrthogonalDesign

/-- Assumption ORT: the design matrix `X` satisfies the orthogonal-design
condition `Xᵀ X = n · I_d`, i.e. its columns are orthogonal and each has
squared norm `n`. -/
structure AssumptionORT {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) : Prop where
  ortho_condition : X.transpose * X = (n : ℕ) • (1 : Matrix (Fin d) (Fin d) ℝ)

end OrthogonalDesign
