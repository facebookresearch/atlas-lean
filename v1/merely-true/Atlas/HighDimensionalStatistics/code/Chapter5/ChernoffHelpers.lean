/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.SparseBallCard

open Finset Real

noncomputable section

namespace SparseVarshamovGilbert

/-- The Hamming ball of radius `2t` centred at a sparse vector `x ∈ {0,1}^d`
of weight `k`, as a finite subset of `SparseVec d k`. -/
def sparseBallRadius (d k t : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val ≤ 2 * t

end SparseVarshamovGilbert

end
