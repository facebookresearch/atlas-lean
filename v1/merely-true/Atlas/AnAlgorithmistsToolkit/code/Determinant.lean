/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

namespace Determinant

open Matrix Equiv.Perm Finset in
theorem det_leibniz_column {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n,
      (Equiv.Perm.sign σ : ℤ) • ∏ i, M i (σ i) := by
  rw [← det_transpose, det_apply]
  congr 1

end Determinant
