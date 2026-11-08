/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec14QCohProjective

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]






/-- The degree-`d` graded piece of `A` packaged as an additive subgroup. -/
def degreePiece (d : ℕ) : AddSubgroup A where
  carrier := (𝒜 d : Set A)
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem (𝒜 d)
  neg_mem' ha := neg_mem ha



end
