/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine

open CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000

namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The sign-change exchange hypothesis: whenever a reduced word $\omega$ makes
$e_s$ into a negative root, there is some position $i$ in $\omega$ such that
deleting it gives a word with product $\mathtt{wordProd}\,\omega \cdot
\mathtt{simple}\,s$. -/
abbrev SignChangeExchangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B) (s : B),
    cs.IsReduced word →
    IsNegative (wordSigma M word (e s)) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

/-- Deprecated bridge construction: builds the geometric bridge hypothesis
from a sign-change exchange hypothesis together with the length-decrease
implies negativity lemma. -/
@[deprecated "Use exchange_condition_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
def geometricBridgeFromNegOfDescent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (hsce : SignChangeExchangeHyp M cs) :
    GeometricBridgeHyp M cs where
  length_decrease_negative := neg_of_descent M cs
  sign_change_exchange := hsce


/-- Deprecated wrapper: the sign-change exchange hypothesis implies the
abstract exchange condition. -/
@[deprecated "Use exchange_condition_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exchange_condition_from_neg_of_descent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (hsce : SignChangeExchangeHyp M cs) :
    SatisfiesExchangeCondition M cs :=
  exchange_from_bridge (geometricBridgeFromNegOfDescent M cs hsce)

end CoxeterExchange
