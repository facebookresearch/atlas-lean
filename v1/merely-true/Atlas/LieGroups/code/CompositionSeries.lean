/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

structure LieModule.CompositionSeries
    (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_mono : ∀ i : Fin length, series i.castSucc < series i.succ





































end
