/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

open scoped Pointwise

namespace AdditiveCombinatorics

/-- For finite subsets `A, B` of an abelian group, the difference sets `B - A` and
`A - B` have the same cardinality, since one is the negation of the other. -/
lemma Finset.card_sub_comm {G : Type*} [DecidableEq G] [AddCommGroup G] (A B : Finset G) :
    (B - A).card = (A - B).card := by
  have h : B - A = -(A - B) := by
    ext x
    simp only [Finset.mem_neg, Finset.mem_sub]
    constructor
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, by simp [neg_sub]⟩
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, hy⟩
      exact ⟨b, hb, a, ha, by rw [← hy]; simp [neg_sub]⟩
  rw [h, Finset.card_neg]

/-- **Ruzsa triangle inequality.** For any finite subsets `A, B, C` of an abelian
group `Z`, $$|A| \cdot |B - C| \le |A - B| \cdot |A - C|.$$ -/
theorem Finset.ruzsa_triangle_inequality {G : Type*} [DecidableEq G] [AddCommGroup G]
    (A B C : Finset G) :
    A.card * (B - C).card ≤ (A - B).card * (A - C).card := by
  have h := _root_.Finset.ruzsa_triangle_inequality_sub_sub_sub B A C
  rw [mul_comm] at h
  rw [Finset.card_sub_comm A B, Finset.card_sub_comm A C] at h
  exact h

end AdditiveCombinatorics
