/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

namespace EGNO.MacLaneCoherence

section FreeMonoidalCoherence

/-- The free monoidal category on a set of objects is a thin category: between any two
parenthesized products there is at most one morphism. This is the core form of
MacLane's coherence theorem. -/
theorem macLane_coherence_free (C : Type*) :
    Quiver.IsThin (FreeMonoidalCategory C) :=
  FreeMonoidalCategory.subsingleton_hom

/-- The full normalization isomorphism in the free monoidal category, witnessing that
every object is canonically isomorphic to its normalized form. -/
def macLane_coherence_normalization (C : Type*) :
    𝟭 (FreeMonoidalCategory C) ≅
      FreeMonoidalCategory.fullNormalize C ⋙ FreeMonoidalCategory.inclusion :=
  FreeMonoidalCategory.fullNormalizeIso C

end FreeMonoidalCoherence

section Theorem_1_9_1

/-- Theorem 1.9.1 (MacLane's Coherence Theorem): Any two morphisms built by composing
associativity and unit isomorphisms (and their inverses, possibly tensored with identities)
between the same source and target in a monoidal category are equal. -/
theorem Theorem_1_9_1 {C : Type*} {D : Type*} [Category D] [MonoidalCategory D]
    (f : C → D) {P₁ P₂ : FreeMonoidalCategory C} (g₁ g₂ : P₁ ⟶ P₂) :
    (FreeMonoidalCategory.project f).map g₁ = (FreeMonoidalCategory.project f).map g₂ := by
  congr 1
  exact Subsingleton.elim g₁ g₂

end Theorem_1_9_1

section CoherenceConsequences

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

end CoherenceConsequences

end EGNO.MacLaneCoherence
