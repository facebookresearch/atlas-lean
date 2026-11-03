/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.ClassEquation

namespace ClassEquation

open Subgroup MulAction ConjClasses

variable {G : Type*} [Group G]

theorem isPGroup_iff_card (p : ℕ) [Fact (Nat.Prime p)] [Finite G] :
    IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n :=
  IsPGroup.iff_card

theorem group_of_order_p_sq_abelian {p : ℕ} [Fact (Nat.Prime p)]
    (hG : Nat.card G = p ^ 2) (a b : G) : a * b = b * a :=
  IsPGroup.commutative_of_card_eq_prime_sq hG a b
