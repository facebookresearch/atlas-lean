/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

open AlgebraicGeometry CategoryTheory Topology

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Characterisation of closed immersions of schemes: `f` is a closed immersion iff its image is
closed, the underlying map is a topological embedding, and every stalk map is surjective. -/
theorem isClosedImmersion_iff_closedRange_embedding_surjectiveOnStalks :
    IsClosedImmersion f ↔
      IsClosed (Set.range f) ∧
      IsEmbedding (f : X → Y) ∧
      ∀ x : X, Function.Surjective (ConcreteCategory.hom (f.stalkMap x)) := by
  rw [isClosedImmersion_iff, surjectiveOnStalks_iff]
  constructor
  · rintro ⟨hsurj, hclosed⟩
    exact ⟨hclosed.isClosed_range, hclosed.isEmbedding, hsurj⟩
  · rintro ⟨hclosed, hemb, hsurj⟩
    exact ⟨hsurj, IsClosedEmbedding.mk hemb hclosed⟩

/-- The image of a closed immersion is a closed subset of the target. -/
theorem IsClosedImmersion.isClosed_range' [IsClosedImmersion f] :
    IsClosed (Set.range f) :=
  f.isClosedEmbedding.isClosed_range

/-- The underlying continuous map of a closed immersion is a topological embedding. -/
theorem IsClosedImmersion.isEmbedding' [IsClosedImmersion f] :
    IsEmbedding (f : X → Y) :=
  f.isClosedEmbedding.isEmbedding

/-- The stalk map of a closed immersion at any point is surjective. -/
theorem IsClosedImmersion.stalkMap_surjective' [IsClosedImmersion f] (x : X) :
    Function.Surjective (ConcreteCategory.hom (f.stalkMap x)) :=
  (surjectiveOnStalks_iff f).mp inferInstance x
