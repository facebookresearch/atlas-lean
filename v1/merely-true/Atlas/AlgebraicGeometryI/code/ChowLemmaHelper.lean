/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace ChowLemmaHelper

/-- Data of a finite affine cover of a scheme `X`, together with closed immersions of each chart
into an ambient affine space; used in the assembly of Chow's lemma. -/
structure AffineCoverData (X : Scheme.{u}) where
  ι : Type u
  [fintype : Fintype ι]
  R : ι → CommRingCat.{u}
  f : (i : ι) → Spec (R i) ⟶ X
  isOpenImmersion : ∀ i, IsOpenImmersion (f i)
  covers : ∀ x : X, ∃ i, x ∈ Set.range (f i).base
  ambientRing : ι → CommRingCat.{u}
  embedding : (i : ι) → Spec (R i) ⟶ Spec (ambientRing i)
  isClosedImmersion : ∀ i, IsClosedImmersion (embedding i)

attribute [instance] AffineCoverData.fintype AffineCoverData.isOpenImmersion

/-- The number of charts in an `AffineCoverData`. -/
def AffineCoverData.card {X : Scheme.{u}} (c : AffineCoverData X) : ℕ :=
  Fintype.card c.ι

/-- Convert `AffineCoverData` into a Mathlib `Scheme.OpenCover`, forgetting the ambient
embeddings. -/
def AffineCoverData.toOpenCover {X : Scheme.{u}} (c : AffineCoverData X) : X.OpenCover where
  I₀ := c.ι
  X i := Spec (c.R i)
  f := c.f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => c.covers x, fun i => c.isOpenImmersion i⟩

/-- The underlying index type of the associated open cover is finite. -/
instance {X : Scheme.{u}} (c : AffineCoverData X) : Fintype c.toOpenCover.I₀ :=
  c.fintype



end ChowLemmaHelper
