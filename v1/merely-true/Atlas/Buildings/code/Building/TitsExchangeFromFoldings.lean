/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.TitsTheoremProof
import Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Atlas.Buildings.code.CoxeterGroup.UnconditionalExchange

open TitsTheoremProof
open CoxeterExchange
open StrongExchangeBridge

variable {B : Type*} [DecidableEq B] [Fintype B]

namespace TitsExchangeFromFoldings

/-- The typed word product accumulator equals left multiplication by the
Coxeter system word product. -/
theorem wordProduct_eq_mul_wordProd (M : CoxeterMatrix B) (w : M.Group)
    (word : List B) :
    wordProduct M w word = w * M.toCoxeterSystem.wordProd word := by
  induction word generalizing w with
  | nil =>
    simp only [wordProduct, CoxeterSystem.wordProd_nil, mul_one]
  | cons i rest ih =>
    simp only [wordProduct, CoxeterSystem.wordProd_cons]
    rw [ih]
    group

/-- Specialization of `wordProduct_eq_mul_wordProd` at $w = 1$. -/
theorem wordProduct_one_eq_wordProd (M : CoxeterMatrix B) (word : List B) :
    wordProduct M 1 word = M.toCoxeterSystem.wordProd word := by
  rw [wordProduct_eq_mul_wordProd, one_mul]

/-- Deletion condition: if a word $s_1 \dots s_n$ is longer than the length of
the element it represents, then two letters can be deleted without changing
the represented Coxeter element. -/
theorem typed_gallery_deletion (M : CoxeterMatrix B)
    (word : List B)
    (hlong : word.length > M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd word)) :
    ∃ (i j : Fin word.length), i < j ∧
      M.toCoxeterSystem.wordProd ((word.eraseIdx j).eraseIdx i) =
        M.toCoxeterSystem.wordProd word :=
  deletion_unconditional M.toCoxeterSystem word hlong

/-- The exchange condition holds unconditionally for any Coxeter system
arising from a Coxeter matrix. -/
theorem exchange_condition (M : CoxeterMatrix B) :
    SatisfiesExchangeCondition M M.toCoxeterSystem :=
  exchange_condition_unconditional M M.toCoxeterSystem

end TitsExchangeFromFoldings
