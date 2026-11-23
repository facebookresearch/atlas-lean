/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine

open AlgebraicGeometry CategoryTheory

universe u

/-- Lecture 4, Definition 9: an *affine morphism* `f : X → Y` of schemes is one for which there
exists an affine open cover of `Y` whose preimages in `X` are affine. -/
abbrev IsAffineMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsAffineHom f

/-- A morphism is affine iff the preimage of every affine open of the target is affine in the
source. -/
theorem isAffineMorphism_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsAffineMorphism f ↔ ∀ (U : Y.Opens), IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U) :=
  isAffineHom_iff f

/-- It suffices to verify the affine-morphism condition pointwise: if every point of `Y` lies in
some affine open whose preimage is affine, then `f` is an affine morphism. -/
theorem isAffineMorphism_of_affine_open_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) :
    IsAffineMorphism f :=
  isAffineHom_of_forall_exists_isAffineOpen f H
