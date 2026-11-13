/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Comma

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Prop17

/-- The "absolute" anti-equivalence between affine schemes and commutative rings:
`AffineScheme ≌ CommRingᵒᵖ` via `Spec`. (Thm 2.1.) -/
noncomputable def absolute : AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ :=
  AffineScheme.equivCommRingCat

/-- The `O_Y`-module underlying an `O_Y`-algebra `A` (with structure map `α : O_Y → A`),
obtained by restriction of scalars from the natural `A`-module structure on `A`. -/
noncomputable def underlyingModule (Y : Scheme.{u}) (A : TopCat.Sheaf CommRingCat.{u} Y)
    (α : Y.sheaf ⟶ A) : Y.Modules :=
  let F := sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)
  (SheafOfModules.restrictScalars (F.map α)).obj (SheafOfModules.unit.{u} (F.obj A))

/-- A *quasi-coherent `O_Y`-algebra*: a sheaf of commutative rings on `Y`, together with a
structure map from `O_Y`, whose underlying `O_Y`-module is quasi-coherent. -/
structure QCohAlg (Y : Scheme.{u}) where
  sheaf : TopCat.Sheaf CommRingCat.{u} Y
  algebraMap : Y.sheaf ⟶ sheaf
  isQCoh : (underlyingModule Y sheaf algebraMap).IsQuasicoherent

/-- A morphism of quasi-coherent `O_Y`-algebras: a map of sheaves of rings commuting with the
structure maps from `O_Y`. -/
@[ext]
structure QCohAlg.Hom {Y : Scheme.{u}} (A B : QCohAlg Y) where
  ringHom : A.sheaf ⟶ B.sheaf
  algebraMap_comp : A.algebraMap ≫ ringHom = B.algebraMap

/-- Category structure on quasi-coherent `O_Y`-algebras. -/
noncomputable instance instCategoryQCohAlg (Y : Scheme.{u}) : Category (QCohAlg Y) where
  Hom := QCohAlg.Hom
  id A := ⟨𝟙 A.sheaf, by simp⟩
  comp f g := ⟨f.ringHom ≫ g.ringHom,
    by rw [← Category.assoc, f.algebraMap_comp, g.algebraMap_comp]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

/-- The category of affine schemes over `Y`: schemes equipped with an affine morphism to `Y`
(Def 9, Lec 2). -/
abbrev AffineSchemeOver (Y : Scheme.{u}) :=
  (MorphismProperty.overObj (W := @IsAffineHom) (X := Y)).FullSubcategory


end Prop17
