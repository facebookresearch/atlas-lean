/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace GraphMatrices

open Matrix SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

noncomputable def singleEdgeLapMatrix (u v : V) : Matrix V V ℝ :=
  Matrix.vecMulVec (Pi.single u 1 - Pi.single v 1 : V → ℝ)
    (Pi.single u 1 - Pi.single v 1 : V → ℝ)

end GraphMatrices
