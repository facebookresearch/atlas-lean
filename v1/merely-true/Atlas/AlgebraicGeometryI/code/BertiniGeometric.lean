/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

namespace BertiniGeometric

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]



/-- The projective hyperplane `V(H) ⊂ ℙ(V)` corresponding to a class `H ∈ ℙ(V*)`: the locus of
points where a representative linear functional vanishes. -/
def projectiveHyperplane (H : Projectivization k (Module.Dual k V)) :
    Set (Projectivization k V) :=
  {p : Projectivization k V | (Projectivization.rep H) (Projectivization.rep p) = 0}



end BertiniGeometric
