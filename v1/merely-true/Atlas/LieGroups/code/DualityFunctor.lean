/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.DualityFunctorDefs
import Atlas.LieGroups.code.BGGReciprocity

noncomputable section

universe uCatO

def IsInjectiveInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (I : Type uCatO) [AddCommGroup I] [Module R I]
    [LieRingModule 𝔤 I] [LieModule R 𝔤 I]
    (_hI : IsCategoryO Δ rd I) : Prop :=
  ∀ (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_ : IsCategoryO Δ rd X),
  ∀ (Y : Type uCatO) [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_ : IsCategoryO Δ rd Y),
  ∀ (i : X →ₗ⁅R, 𝔤⁆ Y) (_ : Function.Injective i)
    (f : X →ₗ⁅R, 𝔤⁆ I),
    ∃ (g : Y →ₗ⁅R, 𝔤⁆ I), ∀ x, g (i x) = f x



end
