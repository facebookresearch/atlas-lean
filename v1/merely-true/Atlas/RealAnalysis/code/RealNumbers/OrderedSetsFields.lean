/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace OrderedSetsFields

/-- **Ordered set.** A type `α` equipped with a relation `lt : α → α → Prop` is
an ordered set if it satisfies trichotomy (for any `x y`, exactly one of `lt x y`,
`lt y x`, or `x = y` holds) and transitivity (`lt x y` and `lt y z` imply `lt x z`). -/
class IsOrderedSet (α : Type*) (lt : α → α → Prop) : Prop where
  trichotomy : ∀ x y : α, lt x y ∨ lt y x ∨ x = y
  transitivity : ∀ x y z : α, lt x y → lt y z → lt x z

/-- **Bounded above and bounded below.** In a preorder, a set `E` is bounded above
iff there exists an upper bound `b` with `x ≤ b` for all `x ∈ E`, and bounded
below iff there exists a lower bound `c` with `c ≤ x` for all `x ∈ E`. -/
theorem bounded_above_below_iff {α : Type*} [Preorder α] (E : Set α) :
    (BddAbove E ↔ ∃ b, ∀ x ∈ E, x ≤ b) ∧ (BddBelow E ↔ ∃ c, ∀ x ∈ E, c ≤ x) := by
  exact ⟨by simp [BddAbove, upperBounds, Set.Nonempty],
         by simp [BddBelow, lowerBounds, Set.Nonempty]⟩

/-- **Least Upper Bound (LUB) Property.** A preordered type `α` has the LUB
property if every nonempty subset `E ⊆ α` that is bounded above has a least
upper bound (supremum) in `α`. -/
def HasLUBProperty (α : Type*) [Preorder α] : Prop :=
  ∀ (E : Set α), E.Nonempty → BddAbove E → ∃ x, IsLUB E x

/-- **Ordered field axioms.** In an ordered field `F`, the order is compatible
with addition (`x < y` implies `x + z < y + z`) and with multiplication
(if `0 < x` and `0 < y`, then `0 < x * y`). -/
theorem ordered_field_axioms (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    (∀ x y z : F, x < y → x + z < y + z) ∧
    (∀ x y : F, 0 < x → 0 < y → 0 < x * y) :=
  ⟨fun _ _ z h => add_lt_add_left h z, fun _ _ hx hy => mul_pos hx hy⟩

end OrderedSetsFields

namespace RealNumbers

/-- **Field axioms.** A field `F` satisfies the addition axioms (A1-A5:
commutativity, associativity, existence of `0`, additive inverses), the
multiplication axioms (M1-M5: commutativity, associativity, existence of `1`,
multiplicative inverses for nonzero elements), and the distributive law (D). -/
theorem field_axioms (F : Type*) [Field F] :
    (∀ x y : F, x + y = y + x) ∧
    (∀ x y z : F, (x + y) + z = x + (y + z)) ∧
    (∃ zero : F, ∀ x, zero + x = x) ∧
    (∀ x : F, ∃ y, x + y = 0) ∧
    (∀ x y : F, x * y = y * x) ∧
    (∀ x y z : F, (x * y) * z = x * (y * z)) ∧
    (∃ one : F, ∀ x, one * x = x) ∧
    (∀ x : F, x ≠ 0 → ∃ y, x * y = 1) ∧
    (∀ x y z : F, (x + y) * z = x * z + y * z) := by
  refine ⟨add_comm, add_assoc, ⟨0, zero_add⟩, fun x => ⟨-x, add_neg_cancel x⟩,
    mul_comm, mul_assoc, ⟨1, one_mul⟩, fun x hx => ⟨x⁻¹, mul_inv_cancel₀ hx⟩, add_mul⟩

end RealNumbers
