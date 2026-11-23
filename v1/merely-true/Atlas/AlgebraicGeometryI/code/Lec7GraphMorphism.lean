/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Function
import Mathlib.Tactic

/-- The graph of a function `f : X → Y` as the subset of `X × Y` of
pairs `(x, f x)` (Lec 7, Def 18). -/
def graphOfMorphism {X Y : Type*} (f : X → Y) : Set (X × Y) :=
  {p | p.2 = f p.1}

/-- The graph of `f` coincides with the range of `x ↦ (x, f x)`. -/
theorem graphOfMorphism_eq_range {X Y : Type*} (f : X → Y) :
    graphOfMorphism f = Set.range (fun x => (x, f x)) := by
  ext ⟨x, y⟩
  simp only [graphOfMorphism, Set.mem_setOf_eq, Set.mem_range, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨x, rfl, h.symm⟩
  · rintro ⟨a, rfl, rfl⟩; rfl
