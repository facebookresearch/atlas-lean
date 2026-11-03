/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace Eigenvalues

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [Field F]

theorem eigenvalue_iff_root_charPoly (A : Matrix n n F) (μ : F) :
    μ ∈ spectrum F A ↔ (Matrix.charpoly A).IsRoot μ :=
  Matrix.mem_spectrum_iff_isRoot_charpoly

open Module

theorem eigenvectors_linearIndependent {ι : Type*} {R : Type*} {M : Type*}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M]
    (f : End R M) (μ : ι → R) (hμ : Function.Injective μ) (v : ι → M)
    (h_eigenvec : ∀ i, f.HasEigenvector (μ i) (v i)) : LinearIndependent R v :=
  f.eigenvectors_linearIndependent' μ hμ v h_eigenvec

end Eigenvalues
