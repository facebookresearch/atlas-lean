/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence
import Atlas.TensorCategories.code.PivotalSpherical
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option maxHeartbeats 1600000

open CategoryTheory MonoidalCategory Module Category

universe u

noncomputable section

variable (k : Type u) [Field k]

namespace TensorCategories

/-- For a finite-dimensional vector space `V` over a field `k`, the dimension of `V`
equals the dimension of its dual `V*`. -/
theorem vec_finrank_dual_eq (V : FGModuleCat.{u} k) :
    Module.finrank k V = Module.finrank k (Vᘁ : FGModuleCat.{u} k) :=
  (Subspace.dual_finrank_eq).symm

end TensorCategories

end
