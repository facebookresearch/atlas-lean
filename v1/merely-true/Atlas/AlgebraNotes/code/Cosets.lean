/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Pointwise

namespace Cosets

variable {G : Type*} [Group G]

theorem coset_eq_of_mem (H : Subgroup G) (a b : G) (hb : b ∈ a • (H : Set G)) :
    a • (H : Set G) = b • (H : Set G) := by
  rw [leftCoset_eq_iff]
  exact (mem_leftCoset_iff a).mp hb

variable (H : Subgroup G)

theorem mem_leftCoset_self (g : G) :
    g ∈ g • (H : Set G) :=
  mem_own_leftCoset H.toSubmonoid g

theorem leftCosets_eq_or_disjoint (a b : G) :
    a • (H : Set G) = b • (H : Set G) ∨ Disjoint (a • (H : Set G)) (b • (H : Set G)) := by
  by_cases h : a⁻¹ * b ∈ H
  · left
    exact (leftCoset_eq_iff H).mpr h
  · right
    rw [Set.disjoint_left]
    intro x hxa hxb
    apply h
    have ha : a⁻¹ * x ∈ (H : Set G) := (mem_leftCoset_iff a).mp hxa
    have hb : b⁻¹ * x ∈ (H : Set G) := (mem_leftCoset_iff b).mp hxb
    have key : a⁻¹ * b = (a⁻¹ * x) * (b⁻¹ * x)⁻¹ := by group
    rw [key]
    exact H.mul_mem ha (H.inv_mem hb)

theorem leftCosets_partition :
    (∀ g : G, ∃ a : G, g ∈ a • (H : Set G)) ∧
    (∀ a b : G, a • (H : Set G) = b • (H : Set G) ∨
      Disjoint (a • (H : Set G)) (b • (H : Set G))) :=
  ⟨fun g => ⟨g, mem_leftCoset_self H g⟩, leftCosets_eq_or_disjoint H⟩

end Cosets
