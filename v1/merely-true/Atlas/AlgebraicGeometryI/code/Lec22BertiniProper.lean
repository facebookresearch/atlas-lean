/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic

section BertiniPredicates

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]


/-- The hyperplane in `ℙ(V)` cut out by a point `H ∈ ℙ(V*)`, namely the zero locus of a
representative linear form. -/
noncomputable def projectiveHyperplane :
    Projectivization k (Module.Dual k V) → Set (Projectivization k V) :=
  fun H => {p : Projectivization k V | (Projectivization.rep H) (Projectivization.rep p) = 0}



end BertiniPredicates



