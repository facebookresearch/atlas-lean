/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-- Definition 24 (Lec 10): a sheaf of `O_X`-modules `F` is quasi-coherent if it is
locally a cokernel of a map between free sheaves; abbreviates `SheafOfModules.IsQuasicoherent`. -/
abbrev IsQuasicoherent_Def24
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R) : Prop :=
  F.IsQuasicoherent
