/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Diagonalization

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isSemisimple_of_squarefree_charpoly (f : End K V)
    (hsq : Squarefree f.charpoly) : f.IsSemisimple :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hsq f.aeval_self_charpoly

theorem isSemisimple_of_charpoly_eq_prod_distinct (f : End K V)
    {ι : Type*} [Fintype ι] (μ : ι → K) (hμ : Function.Injective μ)
    (hprod : f.charpoly = ∏ i, (X - C (μ i))) : f.IsSemisimple := by
  apply isSemisimple_of_squarefree_charpoly
  rw [hprod]
  exact (separable_prod_X_sub_C_iff.mpr hμ).squarefree

end Diagonalization

open Matrix

namespace Matrix

def IsDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] (A : Matrix n n F) : Prop :=
  ∃ (P : Matrix n n F) (_ : Invertible P) (d : n → F), P⁻¹ * A * P = diagonal d
