/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace GroupActions

open MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

def stabilizerSet (G : Type*) [Group G] [MulAction G α] (s : α) : Set G :=
  {g : G | g • s = s}

theorem card_eq_sum_orbit_sizes (G : Type*) (α : Type*) [Group G] [MulAction G α]
    [Fintype α] [Fintype (orbitRel.Quotient G α)]
    [∀ ω : orbitRel.Quotient G α, Fintype ω.orbit] :
    Fintype.card α =
      ∑ ω : orbitRel.Quotient G α, Fintype.card ω.orbit := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (selfEquivSigmaOrbits' G α)

noncomputable def orbitEquivQuotientStabilizer (G : Type*) {α : Type*} [Group G]
    [MulAction G α] (s : α) :
    orbit G s ≃ G ⧸ stabilizer G s :=
  MulAction.orbitEquivQuotientStabilizer G s

theorem card_orbit_eq_index_stabilizer (G : Type*) {α : Type*} [Group G] [MulAction G α]
    (s : α) :
    (stabilizer G s).index = (orbit G s).ncard :=
  MulAction.index_stabilizer G s

end GroupActions
