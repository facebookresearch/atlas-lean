/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.RootSystem

open CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

set_option linter.unusedSectionVars false

/-- Local copy of the generalized reflection along $\beta$:
$s_\beta(v) = v - 2\,B_M(v, \beta)\,\beta$. -/
noncomputable def generalizedReflection_local (M : CoxeterMatrix B) (β : B → ℝ) :
    (B → ℝ) → (B → ℝ) :=
  fun v t => v t - 2 * bilinForm M v β * β t

end CoxeterGroup
