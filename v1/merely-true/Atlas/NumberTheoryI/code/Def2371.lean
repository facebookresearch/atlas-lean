/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Thm2370
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

open CategoryTheory CochainComplex HomComplex Abelian

universe w v u

section GeneralAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

noncomputable def ExtGroup (M A : C) (n : ℕ) : Type w := Ext M A n

noncomputable instance ExtGroup.instAddCommGroup (M A : C) (n : ℕ) :
    AddCommGroup (ExtGroup M A n) :=
  inferInstanceAs (AddCommGroup (Ext M A n))

end GeneralAbelian

section ModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

noncomputable def ExtGroup_R (M A : ModuleCat.{v} R) (n : ℕ) : Type v :=
  ExtGroup M A n

noncomputable instance ExtGroup_R.instAddCommGroup (M A : ModuleCat.{v} R) (n : ℕ) :
    AddCommGroup (ExtGroup_R R M A n) :=
  inferInstanceAs (AddCommGroup (ExtGroup M A n))

end ModuleCat
