/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

open CategoryTheory MonoidalCategory

noncomputable def Prop2369_tensorRight_map_homotopy
    (R : Type*) [CommRing R]
    {ι : Type*} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat R) c}
    {f g : C ⟶ D}
    (A : ModuleCat R)
    (h : Homotopy f g) :
    Homotopy (((tensorRight A).mapHomologicalComplex c).map f)
             (((tensorRight A).mapHomologicalComplex c).map g) :=
  (tensorRight A).mapHomotopy h
