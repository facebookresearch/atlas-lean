/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Additive.Energy

namespace BKTProof

open Pointwise

/-- BKT additive energy proposition: for finite sets `A, B` in an additive group,
`|A|² · |B|² ≤ |A + B| · E(A, B)`, where `E(A, B)` denotes the additive energy of the
pair. This is a thin wrapper around the corresponding Mathlib lemma. -/
theorem card_sq_mul_card_sq_le_card_add_mul_addEnergy
    {α : Type*} [DecidableEq α] [Add α]
    (A B : Finset α) :
    A.card ^ 2 * B.card ^ 2 ≤ (A + B).card * A.addEnergy B :=
  Finset.le_card_add_mul_addEnergy A B

end BKTProof
