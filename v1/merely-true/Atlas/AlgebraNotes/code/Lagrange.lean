/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Lagrange

theorem card_eq_index_mul_card {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card G = H.index * Fintype.card H := by
  have h := Subgroup.index_mul_card H
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  exact h.symm

theorem lagrange_dvd (G : Type*) [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  have := H.card_subgroup_dvd_card
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

theorem lagrange_theorem (G : Type*) [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  have := Subgroup.card_subgroup_dvd_card H
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

theorem counting_formula {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card G = Fintype.card H * H.index := by
  have h := H.card_mul_index
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  omega

end Lagrange
