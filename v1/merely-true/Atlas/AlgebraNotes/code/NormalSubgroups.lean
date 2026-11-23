/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.TFAE

open scoped Pointwise
open MulOpposite

namespace NormalSubgroups

variable {G : Type*} [Group G] (H : Subgroup G)

theorem normal_iff_leftCoset_eq_rightCoset :
    H.Normal ↔ ∀ g : G, g • (H : Set G) = op g • (H : Set G) :=
  normal_iff_eq_cosets H

theorem normal_iff_conj_image_eq :
    H.Normal ↔ ∀ g : G, (MulAut.conj g) '' (H : Set G) = (H : Set G) := by
  constructor
  · intro hN g
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, MulAut.conj_apply]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hN.conj_mem h hh g
    · intro hx
      exact ⟨g⁻¹ * x * g, hN.conj_mem' x hx g, by simp [mul_assoc]⟩
  · intro h
    constructor
    intro n hn g
    have : g * n * g⁻¹ ∈ (MulAut.conj g) '' (H : Set G) :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rw [h g] at this
    exact this

theorem normal_iff_conj_mem :
    H.Normal ↔ ∀ n ∈ H, ∀ g : G, g * n * g⁻¹ ∈ H :=
  ⟨fun hN => hN.conj_mem, fun h => ⟨h⟩⟩

theorem normal_tfae :
    List.TFAE [
      H.Normal,
      ∀ g : G, g • (H : Set G) = op g • (H : Set G),
      ∀ g : G, (MulAut.conj g) '' (H : Set G) = (H : Set G),
      ∀ n ∈ H, ∀ g : G, g * n * g⁻¹ ∈ H
    ] := by
  tfae_have 1 ↔ 2 := normal_iff_leftCoset_eq_rightCoset H
  tfae_have 1 ↔ 3 := normal_iff_conj_image_eq H
  tfae_have 1 ↔ 4 := normal_iff_conj_mem H
  tfae_finish

end NormalSubgroups
