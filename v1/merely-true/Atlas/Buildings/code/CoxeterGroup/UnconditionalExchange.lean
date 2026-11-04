/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.SignChangeExchangeFinal
import Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge
import Atlas.Buildings.code.CoxeterGroup.ExchangeConditionProof

open CoxeterExchange CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000


namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- **Unconditional exchange condition** for any Coxeter system. -/
theorem exchange_condition_unconditional {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) :
    SatisfiesExchangeCondition M cs :=
  exchange_condition_from_neg_of_descent M cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

/-- **Unconditional deletion condition** for any Coxeter system. -/
theorem deletion_unconditional {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) :
    SatisfiesDeletionCondition M cs :=
  deletion_of_exchange cs (exchange_condition_unconditional M cs)

/-- The corollary of the exchange condition, made unconditional. -/
theorem corollary_unconditional {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) :
    ExchangeCorollary M cs :=
  corollary_of_exchange cs (exchange_condition_unconditional M cs)

/-- Combined: the exchange condition, deletion condition, and exchange corollary all hold
unconditionally for any Coxeter system. -/
theorem all_unconditional {W : Type*} [Group W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) :
    SatisfiesExchangeCondition M cs ∧
    SatisfiesDeletionCondition M cs ∧
    ExchangeCorollary M cs :=
  let hex := exchange_condition_unconditional M cs
  ⟨hex, deletion_of_exchange cs hex, corollary_of_exchange cs hex⟩


variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Exchange ⇒ deletion, applied unconditionally via the sign-change hypothesis. -/
theorem exchange_implies_deletion_unconditional :
    SatisfiesDeletionCondition M cs :=
  exchange_implies_deletion cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

/-- Exchange ⇒ corollary, applied unconditionally. -/
theorem exchange_implies_corollary_unconditional :
    ExchangeCorollary M cs :=
  exchange_implies_corollary cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

/-- Exchange ⇒ both deletion and corollary, packaged unconditionally. -/
theorem exchange_implies_both_unconditional :
    SatisfiesDeletionCondition M cs ∧ ExchangeCorollary M cs :=
  exchange_implies_both cs
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)

end CoxeterExchange


namespace StrongExchangeBridge

variable {W : Type*} [Group W] {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {cs : CoxeterSystem M W}

/-- Unconditional exchange-by-erase: removing an index from a reduced word with $s$ a right descent
yields a reduced word with product $w \cdot s$. -/
theorem exchange_descent_eraseIdx_unconditional
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
    ∃ i : Fin word.length,
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s ∧
      cs.IsReduced (word.eraseIdx i) :=
  exchange_descent_eraseIdx
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)
    word s hred hdesc

/-- Unconditional version: when $s$ is a right descent, there is a reduced word ending in $s$ with the same product. -/
theorem exists_reduced_ending_in_unconditional
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
    ∃ (prefix_word : List B),
      cs.IsReduced (prefix_word ++ [s]) ∧
      cs.wordProd (prefix_word ++ [s]) = cs.wordProd word ∧
      prefix_word.length + 1 = word.length :=
  exists_reduced_ending_in
    (CoxeterSignChangeExchangeFinal.signChangeExchangeHyp_unconditional M cs)
    word s hred hdesc

end StrongExchangeBridge
