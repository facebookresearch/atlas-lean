/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.WittTheorem

namespace Garrett

/-- Witt cancellation holds for any nondegenerate symmetric bilinear form on a
finite-dimensional space (in characteristic not two). -/
theorem wittCancellation_independent
    {k : Type*} [Field k] [NeZero (2 : k)]
    {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (hSym : ∀ x y : V, B x y = B y x)
    (hNd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
    WittCancellationProp B :=
  wittCancellationProp_of_symmetric B hSym hNd

end Garrett
