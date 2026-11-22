/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CompositionSeries

noncomputable section

universe uCatO

structure CartanInvolution
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) where
  τ : 𝔤 →ₗ[R] 𝔤
  involution : τ ∘ₗ τ = LinearMap.id
  negate_cartan : ∀ h : Δ.𝔥, τ (h : 𝔤) = -(h : 𝔤)
  anti_hom : ∀ (X Y : 𝔤), τ ⁅X, Y⁆ = ⁅τ Y, τ X⁆

structure DualInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X) where
  Xdual : Type uCatO
  [instAddCommGroup : AddCommGroup Xdual]
  [instModule : Module R Xdual]
  [instLieRingModule : LieRingModule 𝔤 Xdual]
  [instLieModule : LieModule R 𝔤 Xdual]
  isCategoryO : IsCategoryO Δ rd Xdual

attribute [instance] DualInO.instAddCommGroup DualInO.instModule
  DualInO.instLieRingModule DualInO.instLieModule



def IsContragredientVerma
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hM : IsCategoryO Δ rd M) : Prop :=
  ∃ (Mlam : Type uCatO) (_ : AddCommGroup Mlam) (_ : Module R Mlam)
    (_ : LieRingModule 𝔤 Mlam) (_ : LieModule R 𝔤 Mlam),
    Nonempty (IsVermaModule Δ Mlam lam) ∧ IsCategoryO Δ rd Mlam ∧
    (∃ (β : M →ₗ[R] Mlam →ₗ[R] R),
      (∀ (x : 𝔤) (m : M) (m' : Mlam), β (⁅x, m⁆) m' + β m ⁅x, m'⁆ = 0) ∧
      (∀ m : M, (∀ m' : Mlam, β m m' = 0) → m = 0) ∧
      (∀ m' : Mlam, (∀ m : M, β m m' = 0) → m' = 0))









end
