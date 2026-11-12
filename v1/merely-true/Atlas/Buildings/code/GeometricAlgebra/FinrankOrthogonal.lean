/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation

open LinearMap (BilinForm)
open Module FiniteDimensional

namespace Garrett

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a nondegenerate bilinear form `B` (in Garrett's sense
`IsNondegenerate' B`) on a finite-dimensional space, the orthogonal complement
of a subspace `W` has dimension `dim V − dim W`. -/
theorem finrank_orthogonal_of_IsNondegenerate'
    (B : BilinForm k V)
    (hB : BilinForm.IsNondegenerate' B)
    (W : Submodule k V) :
    finrank k (B.orthogonal W) = finrank k V - finrank k W :=
  LinearMap.BilinForm.finrank_orthogonal (IsNondegenerate'_to_Nondegenerate_inline hB) W

/-- Same dimension formula but stated with the Mathlib `Nondegenerate`
hypothesis: `dim (W^⊥) = dim V − dim W` for nondegenerate `B`. -/
theorem finrank_orthogonal_of_Nondegenerate'
    {B : BilinForm k V}
    (hB : B.Nondegenerate)
    (W : Submodule k V) :
    finrank k (B.orthogonal W) = finrank k V - finrank k W :=
  LinearMap.BilinForm.finrank_orthogonal hB W

/-- Additive form of the dimension formula: for nondegenerate `B`, the dimensions
of `W` and of its orthogonal complement sum to `dim V`. -/
theorem finrank_add_finrank_orthogonal_of_IsNondegenerate'
    (B : BilinForm k V)
    (hB : BilinForm.IsNondegenerate' B)
    (W : Submodule k V) :
    finrank k W + finrank k (B.orthogonal W) = finrank k V := by
  have h := finrank_orthogonal_of_IsNondegenerate' B hB W
  have hle : finrank k W ≤ finrank k V := Submodule.finrank_le W
  omega

end Garrett
