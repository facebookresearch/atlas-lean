/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
import Atlas.Buildings.code.CoxeterGroup.InversionSet

open Finset BigOperators CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The geometric action $\mathrm{wordSigma}$ depends only on the group element, not the word:
if $\mathrm{wordProd}(w_1) = \mathrm{wordProd}(w_2)$ then $w_1 \cdot v = w_2 \cdot v$. -/
theorem wordSigma_eq_of_wordProd_eq (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (word1 word2 : List B)
    (h : cs.wordProd word1 = cs.wordProd word2) (v : B → ℝ) :
    wordSigma M word1 v = wordSigma M word2 v := by
  have h1 := coxeterRepresentation_wordProd_apply M cs word1 v
  have h2 := coxeterRepresentation_wordProd_apply M cs word2 v
  rw [h] at h1
  rw [← h1, ← h2]

end CoxeterGroup
