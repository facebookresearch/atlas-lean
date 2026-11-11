/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup

open Subgroup

namespace CyclicGroups

variable {G : Type*} [Group G] (g : G)

theorem cyclic_subgroup_structure :
    (orderOf g = 0 ∧ Function.Injective (fun n : ℤ => g ^ n)) ∨
    (0 < orderOf g ∧ Nat.card (zpowers g) = orderOf g) := by
  rcases eq_or_lt_of_le (Nat.zero_le (orderOf g)) with h | h
  · left
    exact ⟨h.symm, injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp h.symm)⟩
  · right
    exact ⟨h, Nat.card_zpowers g⟩
