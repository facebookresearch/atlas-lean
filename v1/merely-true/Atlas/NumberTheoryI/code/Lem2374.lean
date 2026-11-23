/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Def2371
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

open CategoryTheory CochainComplex HomComplex Abelian

universe w v u

section GeneralAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

end GeneralAbelian

section ModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

noncomputable def ext0_addEquiv_hom (M A : ModuleCat.{v} R) :
    ExtGroup_R R M A 0 ≃+ (M ⟶ A) :=
  Ext.addEquiv₀

end ModuleCat
