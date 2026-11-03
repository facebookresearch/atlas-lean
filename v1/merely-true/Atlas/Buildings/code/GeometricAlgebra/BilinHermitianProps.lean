/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Atlas.Buildings.code.GeometricAlgebra.KernelDecomposition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace Formalization.GeometricAlgebra

open Garrett

variable {k : Type*} [Field k] [Invertible (2 : k)]


section Prop2

variable {V : Type*} [AddCommGroup V] [Module k V]

end Prop2


section Prop3


end Prop3


section Prop4

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- An alternating bilinear form is skew-symmetric: `B x y = -(B y x)`. -/
lemma isAlt_skew (B : LinearMap.BilinForm k V) (hAlt : B.IsAlt) (x y : V) :
    B x y = -(B y x) := by
  have h1 := hAlt (x + y)
  simp only [map_add, LinearMap.add_apply] at h1
  rw [hAlt x, hAlt y, zero_add, add_zero] at h1

  rw [add_comm] at h1
  exact add_eq_zero_iff_eq_neg.mp h1

end Prop4

end Formalization.GeometricAlgebra
