/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.SigmaOrder

open CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

set_option linter.unusedSectionVars false

/-- The endomorphism of $\mathbb{R}^B$ associated to a word $s_1 \cdots s_k$,
defined as the product $\sigma_{s_1} \circ \cdots \circ \sigma_{s_k}$ in
$\mathrm{End}_{\mathbb{R}}(\mathbb{R}^B)$. -/
noncomputable def sigmaWord (M : CoxeterMatrix B) : List B → Module.End ℝ (B → ℝ)
  | [] => 1
  | s :: rest => sigmaLin M s * sigmaWord M rest

/-- Cons unfolding of `sigmaWord`. -/
@[simp] theorem sigmaWord_cons (M : CoxeterMatrix B) (s : B) (w : List B) :
    sigmaWord M (s :: w) = sigmaLin M s * sigmaWord M w := rfl

/-- Singleton: `sigmaWord M [s] = sigmaLin M s`. -/
theorem sigmaWord_singleton (M : CoxeterMatrix B) (s : B) :
    sigmaWord M [s] = sigmaLin M s := by simp [sigmaWord]

end CoxeterGroup
