/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.DualityFunctor

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def ExtVanishes_CategoryO
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) :
    ℕ →
    (X : Type uCatO) → [AddCommGroup X] → [Module R X] →
    [LieRingModule 𝔤 X] → [LieModule R 𝔤 X] →
    IsCategoryO Δ rd X →
    (Y : Type uCatO) → [AddCommGroup Y] → [Module R Y] →
    [LieRingModule 𝔤 Y] → [LieModule R 𝔤 Y] →
    IsCategoryO Δ rd Y → Prop
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => True
  | 1, X, _, _, _, _, _hXO, Y, _, _, _, _, _hYO =>
    ∀ (E : Type uCatO) [AddCommGroup E] [Module R E]
      [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
      (_hEO : IsCategoryO Δ rd E)
      (ι : Y →ₗ⁅R, 𝔤⁆ E) (_hι : Function.Injective ι)
      (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
      (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : Y, ι m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x
  | n + 2, X, _, _, _, _, hXO, Y, _, _, _, _, _hYO =>
    ∀ (I : Type uCatO) [AddCommGroup I] [Module R I]
      [LieRingModule 𝔤 I] [LieModule R 𝔤 I]
      (_hIO : IsCategoryO Δ rd I)
      (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
      [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
      (hQO : IsCategoryO Δ rd Q)
      (ι : Y →ₗ⁅R, 𝔤⁆ I) (_hι : Function.Injective ι)
      (p : I →ₗ⁅R, 𝔤⁆ Q) (_hp : Function.Surjective p),
      ExtVanishes_CategoryO rd (n + 1) X hXO Q hQO


theorem projective_implies_ext1_vanishes
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXproj : IsProjectiveInO rd X hXO)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y) :
    ExtVanishes_CategoryO rd 1 X hXO Y hYO := by
  intro E _ _ _ _ hEO ι _hι p hp _hexact
  exact hXproj E hEO X hXO p hp (LieModuleHom.id : X →ₗ⁅R, 𝔤⁆ X)





end
