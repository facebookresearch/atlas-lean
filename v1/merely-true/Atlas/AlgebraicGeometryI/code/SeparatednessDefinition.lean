/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SeparatednessDefinition

variable (k : Type u) [Field k]

/-- The base scheme `Spec k` for varieties over a field `k`. -/
noncomputable abbrev SpecK : Scheme.{u} := Spec (CommRingCat.of k)

/-- A `k`-variety `X` (with structure morphism `f : X → Spec k`) is
*separated* when `f` is a separated morphism. -/
abbrev IsSeparatedVariety {X : Scheme.{u}} (f : X ⟶ SpecK k) : Prop :=
  IsSeparated f

/-- The diagonal morphism `Δ : X → X ×_{Spec k} X` of a `k`-variety. -/
noncomputable def diagonalMorphism {X : Scheme.{u}} (f : X ⟶ SpecK k) :
    X ⟶ pullback f f :=
  pullback.diagonal f

/-- Separatedness criterion: a `k`-variety is separated iff its diagonal
morphism `Δ : X → X × X` is a closed immersion. -/
theorem isSeparatedVariety_iff_diagonal_isClosedImmersion
    {X : Scheme.{u}} (f : X ⟶ SpecK k) :
    IsSeparatedVariety k f ↔ IsClosedImmersion (diagonalMorphism k f) :=
  isSeparated_iff f

/-- Any affine `k`-variety is separated. -/
theorem affine_isSeparated {X : Scheme.{u}} [IsAffine X] (f : X ⟶ SpecK k) :
    IsSeparatedVariety k f :=
  inferInstance

/-- For an affine `k`-variety, the diagonal is automatically a closed
immersion. -/
theorem affine_diagonal_isClosedImmersion {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ SpecK k) :
    IsClosedImmersion (diagonalMorphism k f) :=
  (isSeparatedVariety_iff_diagonal_isClosedImmersion k f).mp (affine_isSeparated k f)

end SeparatednessDefinition
