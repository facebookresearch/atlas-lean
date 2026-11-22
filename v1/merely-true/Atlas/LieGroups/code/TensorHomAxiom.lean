/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryO

open scoped TensorProduct

noncomputable section

universe u


theorem postcomp_surjective_of_free
    {R : Type u} [CommRing R]
    {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Free R V]
    {X : Type u} [AddCommGroup X] [Module R X]
    {Y : Type u} [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y)
    (hf : Function.Surjective f) :
    Function.Surjective (fun (φ : V →ₗ[R] X) => f.comp φ) := by
  intro ψ

  have : Module.Projective R V := Module.Projective.of_free
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f ψ hf
  exact ⟨φ, by ext v; exact LinearMap.congr_fun hφ v⟩


def lieModuleHomPostcomp
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    (V →ₗ[R] M) →ₗ⁅R, 𝔤⁆ (V →ₗ[R] N) where
  toLinearMap :=
    { toFun := fun φ => (f : M →ₗ[R] N).comp φ
      map_add' := fun φ ψ => by ext; simp [LinearMap.add_apply]
      map_smul' := fun r φ => by ext; simp [LinearMap.smul_apply] }
  map_lie' := by
    intro x φ
    ext v
    simp only [LieHom.lie_apply, LinearMap.comp_apply,
      LieModuleHom.coe_toLinearMap]

    rw [map_sub]
    congr 1
    exact LieModuleHom.map_lie f x (φ v)

def lieModuleHomFlip
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (ψ : V →ₗ⁅R, 𝔤⁆ (P →ₗ[R] N)) :
    P →ₗ⁅R, 𝔤⁆ (V →ₗ[R] N) where
  toLinearMap :=
    { toFun := fun p =>
        { toFun := fun v => ψ v p
          map_add' := fun v₁ v₂ => by simp [map_add, LinearMap.add_apply]
          map_smul' := fun r v => by simp [map_smul, LinearMap.smul_apply] }
      map_add' := fun p₁ p₂ => by ext v; simp [LinearMap.add_apply, map_add]
      map_smul' := fun r p => by ext v; simp [LinearMap.smul_apply, map_smul] }
  map_lie' := by
    intro x p
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieHom.lie_apply]

    have h1 := LieModuleHom.map_lie ψ x v
    have h2 : (⁅x, (ψ v : P →ₗ[R] N)⁆ : P →ₗ[R] N) p = ⁅x, (ψ v) p⁆ - (ψ v) ⁅x, p⁆ :=
      LieHom.lie_apply (ψ v) x p
    have h3 : (ψ ⁅x, v⁆) p = ⁅x, (ψ v) p⁆ - (ψ v) ⁅x, p⁆ := by
      have := congr_arg (· p) h1
      dsimp at this; rw [this]
    rw [h3, sub_sub_cancel]


end
