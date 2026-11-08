/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.EpiMono
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Widesubcategory

namespace AlgebraicTopologyI

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- **Definition 4.2 (Simplicial object).**  A simplicial object in a
category `C` is a functor `Δ^{op} → C` from the opposite of the simplex
category.  This is a thin wrapper around Mathlib's
`CategoryTheory.SimplicialObject`. -/
abbrev SimplicialObject (C : Type u) [Category.{v} C] := CategoryTheory.SimplicialObject C

/-- **Definition 4.3 (Injective simplex category).**  The wide subcategory
of `SimplexCategory` whose morphisms are the injective (monomorphism)
simplex maps.  Equivalent to the subcategory of strictly order-preserving
maps `[m] → [n]`. -/
abbrev SimplexCategoryInj :=
  WideSubcategory (MorphismProperty.monomorphisms SimplexCategory)

/-- **Definition 4.5 (Split epimorphism).**  A morphism `f : A ⟶ B` is a
*split epimorphism* if it admits a right inverse, i.e. there exists
`s : B ⟶ A` with `s ≫ f = 𝟙 B`.  Thin wrapper around
`CategoryTheory.IsSplitEpi`. -/
abbrev IsSplitEpi {A B : C} (f : A ⟶ B) := CategoryTheory.IsSplitEpi f

/-- **Definition 4.5 (Split monomorphism).**  A morphism `f : X ⟶ Y` is a
*split monomorphism* if it admits a left inverse, i.e. there exists
`r : Y ⟶ X` with `f ≫ r = 𝟙 X`.  Thin wrapper around
`CategoryTheory.SplitMono`. -/
abbrev SplitMonomorphism {X Y : C} (f : X ⟶ Y) := CategoryTheory.SplitMono f

section FunctorsPreserveSplit

universe v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- **Lemma 4.7 (Split epis are preserved by functors), first half.**  If
`f : X ⟶ Y` is a split epimorphism in `C`, then `F.map f` is a split
epimorphism in `D` for any functor `F : C ⥤ D`.  Functors preserve any
diagram involving only composition and identities, so they automatically
preserve splittings. -/
theorem functor_map_isSplitEpi {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsSplitEpi (F.map f) :=
  inferInstance

/-- **Lemma 4.7 (Split monos are preserved by functors), second half.**  If
`f : X ⟶ Y` is a split monomorphism in `C`, then `F.map f` is a split
monomorphism in `D` for any functor `F : C ⥤ D`. -/
theorem functor_map_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsSplitMono (F.map f) :=
  inferInstance

/-- **Lemma 4.7 (Functors preserve splittings).**  Packaged form of the two
preceding theorems: any functor `F : C ⥤ D` sends split epimorphisms to
split epimorphisms and split monomorphisms to split monomorphisms. -/
theorem functor_preserves_split {X Y : C} (f : X ⟶ Y) :
    (IsSplitEpi f → IsSplitEpi (F.map f)) ∧ (IsSplitMono f → IsSplitMono (F.map f)) :=
  ⟨fun _ => functor_map_isSplitEpi F f, fun _ => functor_map_isSplitMono F f⟩

end FunctorsPreserveSplit

/-- **Lemma 4.8.**  A morphism `f : X ⟶ Y` in a category is an isomorphism
if and only if it is *both* a split epimorphism and a split monomorphism.
The forward direction is immediate (an inverse is a one-sided inverse on
each side).  The reverse direction uses that a monic split epimorphism is
automatically iso. -/
theorem isIso_iff_isSplitEpi_and_isSplitMono {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ IsSplitEpi f ∧ IsSplitMono f := by
  constructor
  · intro h
    exact ⟨IsSplitEpi.of_iso f, IsSplitMono.of_iso f⟩
  · rintro ⟨hse, hsm⟩
    haveI := hse
    haveI := hsm
    exact isIso_of_mono_of_isSplitEpi f

end AlgebraicTopologyI
