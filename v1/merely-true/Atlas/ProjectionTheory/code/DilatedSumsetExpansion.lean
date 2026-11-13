/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.PolyK
import Atlas.ProjectionTheory.code.ContagiousStructure
import Atlas.ProjectionTheory.code.DoubleCountingFF

open Pointwise

namespace ProjectionTheory

/--
The sum-product set `A + A·A = {a + b·c : a, b, c ∈ A}` of a finite subset
`A ⊆ 𝔽_p`.
-/
noncomputable def sumProductSet {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.biUnion (fun a => A.biUnion (fun b => A.image (fun c => a + b * c)))

/--
For any `t ∈ A`, the dilated sumset `A + t·A` is contained in the sum-product
set `A + A·A`.
-/
lemma dilated_sumset_subset_sumProductSet {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) (t : ZMod p) (ht : t ∈ A) :
    A + t • A ⊆ sumProductSet A := by
  intro x hx
  simp only [Finset.mem_add, Finset.mem_smul_finset] at hx
  obtain ⟨a, ha, y, ⟨c, hc, rfl⟩, rfl⟩ := hx
  simp only [sumProductSet, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨a, ha, t, ht, c, hc, rfl⟩

end ProjectionTheory
