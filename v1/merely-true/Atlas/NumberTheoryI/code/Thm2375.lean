/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.LeftDerived

open CategoryTheory Category

universe v u

noncomputable def tor_well_defined
    {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
    [Abelian C] [HasProjectiveResolutions C] [Abelian D]
    {M : C} (P Q : ProjectiveResolution M) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (HomologicalComplex.homologyFunctor D _ n).obj
      ((F.mapHomologicalComplex _).obj P.complex) ≅
    (HomologicalComplex.homologyFunctor D _ n).obj
      ((F.mapHomologicalComplex _).obj Q.complex) :=
  (P.isoLeftDerivedObj F n).symm ≪≫ Q.isoLeftDerivedObj F n


noncomputable alias theorem_23_75 := tor_well_defined
