/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Pointed topological spaces

This file defines pointed topological spaces and their associated topological pairs.
-/

@[expose] public section

open CategoryTheory Topology

universe u

/-- Topological spaces equipped with a distinguished point and basepoint-preserving maps. -/
abbrev PointedTopCat := Under (TopCat.of PUnit)

/-- Adjoin a disjoint basepoint to a topological space. -/
noncomputable abbrev PointedTopCat.addBasepoint := Under.costar (TopCat.of PUnit)

namespace PointedTopCat

noncomputable section

set_option autoImplicit false
set_option warningAsError true

open scoped OnePoint

/-- The one-point compactification of a space, pointed at infinity. -/
abbrev onePointPointed (X : Type u) [TopologicalSpace X] :
    PointedTopCat.{u} :=
  Under.mk (TopCat.ofHom
    (ContinuousMap.const PUnit (∞ : OnePoint X)))

@[simp]
theorem onePointPointed_basepoint
    (X : Type u) [TopologicalSpace X] :
    (onePointPointed X).hom PUnit.unit = (∞ : OnePoint X) :=
  rfl

/-- A homeomorphism extends by sending infinity to infinity. -/
def onePointPointedIsoOfHomeomorph {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : onePointPointed A ≅ onePointPointed B :=
  Under.isoMk (TopCat.isoOfHomeo e.onePointCongr) (by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    rfl)

end

/-- A based map sends the source basepoint to the target basepoint. -/
@[simp]
theorem map_basepoint {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    f.right (X.hom PUnit.unit) = Y.hom PUnit.unit :=
  ConcreteCategory.congr_hom f.w PUnit.unit

/-- Regard a pointed space as the topological pair consisting of its basepoint inclusion. -/
def pointedPair : PointedTopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of X.hom (Topology.IsEmbedding.of_subsingleton X.hom)
  map {X Y} f := TopPair.ofHom f.right (𝟙 _) ((Category.id_comp _).trans f.w.symm)
  map_id X := by ext <;> rfl
  map_comp {X Y Z} f g := by ext <;> rfl

end PointedTopCat
