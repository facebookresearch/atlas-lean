/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

open CategoryTheory Category

universe u v

section Additive_ProjectiveResolutions

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

set_option maxHeartbeats 400000 in
instance projectiveResolutions_additive : Functor.Additive (projectiveResolutions C) where
  map_add {X Y f g} := by
    dsimp [projectiveResolutions]
    suffices h : (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y)) =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
         ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) by
      rw [h]
      exact (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map_add
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftHomotopy (f + g)
    · exact ProjectiveResolution.lift_commutes (f + g) _ _
    · rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes f,
          ProjectiveResolution.lift_commutes g,
          ← Preadditive.comp_add, ← Functor.map_add]

end Additive_ProjectiveResolutions

section Additive_LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type*} [Category D] [Abelian D]

instance leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

end Additive_LeftDerived

section Lemma_23_77

variable (R : Type u) [CommRing R]

instance lemma_23_77 (n : ℕ) (M : ModuleCat.{u} R) :
    Functor.Additive ((Tor (ModuleCat.{u} R) n).obj M) := by
  dsimp [Tor]
  infer_instance

end Lemma_23_77
