/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Def2371
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

open CategoryTheory Abelian

universe w v u

section GeneralAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

end GeneralAbelian

section ModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

noncomputable def lemma_23_73_R_second
    (M A B : ModuleCat.{v} R) (n : ℕ) :
    ExtGroup_R R M (A ⊞ B) n ≃+ ExtGroup_R R M A n × ExtGroup_R R M B n :=
  Ext.addEquivBiprod

end ModuleCat
