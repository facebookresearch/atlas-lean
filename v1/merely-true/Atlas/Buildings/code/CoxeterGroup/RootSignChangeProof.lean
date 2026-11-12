/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Atlas.Buildings.code.CoxeterGroup.SigmaOrder
import Mathlib.GroupTheory.Coxeter.Inversion

open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace CoxeterRootSignChange

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Dropping the first $j$ letters of a reduced word yields another reduced word. -/
lemma isReduced_drop {W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) {word : List B} (hred : cs.IsReduced word) (j : ℕ) :
    cs.IsReduced (word.drop j) := by
  unfold CoxeterSystem.IsReduced
  have htake := cs.length_wordProd_le (word.take j)
  have hdrop := cs.length_wordProd_le (word.drop j)
  have hprod : cs.wordProd word = cs.wordProd (word.take j) * cs.wordProd (word.drop j) := by
    rw [← CoxeterSystem.wordProd_append, List.take_append_drop]
  have hcat : cs.length (cs.wordProd word) ≤
      cs.length (cs.wordProd (word.take j)) + cs.length (cs.wordProd (word.drop j)) := by
    rw [hprod]; exact cs.length_mul_le _ _
  have hlen : word.length = (word.take j).length + (word.drop j).length := by
    rw [← List.length_append, List.take_append_drop]
  rw [hred] at hcat; omega

/-- Geometric root sign change hypothesis derived from the geometric bridge, packaging the
fact that the simple reflection $\sigma_s$ flips a positive root at the descent index. -/
noncomputable def rootSignChangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (bridge : GeometricBridgeHyp M cs) :
    RootSignChangeHyp M cs where
  sign_change_at_index := by
    intro word s _k hred _hk hneg _hgt _hle


    exact bridge.sign_change_exchange word s hred hneg

end CoxeterRootSignChange
