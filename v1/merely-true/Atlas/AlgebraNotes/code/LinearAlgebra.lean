/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank

variable {F : Type*} [Field F]

namespace LinearAlgebra

open Matrix in
theorem rank_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n F) : M.rank = Mᵀ.rank :=
  (Matrix.rank_transpose M).symm

end LinearAlgebra
