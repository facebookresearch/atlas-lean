/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace GroupHomomorphisms

variable {G G' : Type*} [Group G] [Group G']

theorem mul_preserving_map_one (f : G → G') (hf : ∀ a b : G, f (a * b) = f a * f b) :
    f 1 = 1 := by
  have h : f 1 * f 1 = f 1 * 1 := by
    calc f 1 * f 1 = f (1 * 1) := (hf 1 1).symm
      _ = f 1 := by rw [mul_one]
      _ = f 1 * 1 := (mul_one _).symm
  exact mul_left_cancel h

theorem mul_preserving_map_inv (f : G → G') (hf : ∀ a b : G, f (a * b) = f a * f b) (a : G) :
    f a⁻¹ = (f a)⁻¹ := by
  have hone : f 1 = 1 := mul_preserving_map_one f hf
  have h : f a * f a⁻¹ = f a * (f a)⁻¹ := by
    calc f a * f a⁻¹ = f (a * a⁻¹) := (hf a a⁻¹).symm
      _ = f 1 := by rw [mul_inv_cancel]
      _ = 1 := hone
      _ = f a * (f a)⁻¹ := (mul_inv_cancel _).symm
  exact mul_left_cancel h

theorem mul_preserving_map_properties (f : G → G') (hf : ∀ a b : G, f (a * b) = f a * f b) :
    f 1 = 1 ∧ ∀ a : G, f a⁻¹ = (f a)⁻¹ :=
  ⟨mul_preserving_map_one f hf, fun a => mul_preserving_map_inv f hf a⟩

def GroupHomomorphism (G G' : Type*) [Group G] [Group G'] := G →* G'

theorem card_eq_card_ker_mul_card_range [Fintype G] [Fintype G'] (f : G →* G')
    [Fintype f.ker] [Fintype f.range] :
    Fintype.card G = Fintype.card f.ker * Fintype.card f.range := by
  classical
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  rw [h, mul_comm]
  congr 1
  exact Fintype.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

end GroupHomomorphisms
