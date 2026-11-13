/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring

open CoxeterGroup CoxeterExchangeGenuine

namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]
  {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)


/-- Deprecated wrapper deriving the deletion condition from the sign-change
exchange hypothesis (use the unconditional version instead). -/
@[deprecated "Use exchange_implies_deletion_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exchange_implies_deletion
    (hsce : SignChangeExchangeHyp M cs) :
    SatisfiesDeletionCondition M cs :=
  deletion_of_exchange cs (exchange_condition_from_neg_of_descent M cs hsce)

/-- Deprecated wrapper deriving the exchange corollary from the sign-change
exchange hypothesis (use the unconditional version instead). -/
@[deprecated "Use exchange_implies_corollary_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exchange_implies_corollary
    (hsce : SignChangeExchangeHyp M cs) :
    ExchangeCorollary M cs :=
  corollary_of_exchange cs (exchange_condition_from_neg_of_descent M cs hsce)

/-- Deprecated combined wrapper: the sign-change exchange hypothesis implies
both the deletion condition and the exchange corollary. -/
@[deprecated "Use exchange_implies_both_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
theorem exchange_implies_both
    (hsce : SignChangeExchangeHyp M cs) :
    SatisfiesDeletionCondition M cs ∧ ExchangeCorollary M cs :=
  let hex := exchange_condition_from_neg_of_descent M cs hsce
  ⟨deletion_of_exchange cs hex, corollary_of_exchange cs hex⟩

end CoxeterExchange
