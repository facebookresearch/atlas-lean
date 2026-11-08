/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace Garrett

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The radical of a bilinear form is the orthogonal complement of the whole space:
the set of vectors orthogonal to everything. -/
def BilinFormRadical (B : LinearMap.BilinForm k V) : Submodule k V :=
  LinearMap.BilinForm.orthogonal B ⊤

/-- A bilinear form is nondegenerate (in Garrett's sense) when its radical is the
zero subspace. -/
def BilinFormIsNondegenerate (B : LinearMap.BilinForm k V) : Prop :=
  BilinFormRadical B = ⊥


/-- The isometry group of a bilinear form `B`: linear automorphisms `g` of `V`
satisfying `B (g v₁) (g v₂) = B v₁ v₂` for all `v₁, v₂`. -/
def IsometryGroup (B : LinearMap.BilinForm k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {g | ∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    intro v₁ v₂
    simp only [LinearEquiv.mul_apply]
    rw [ha (b v₁) (b v₂), hb v₁ v₂]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro v₁ v₂; simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    intro v₁ v₂
    have key := hg (g⁻¹ v₁) (g⁻¹ v₂)
    simp at key
    exact key.symm


/-- The similitude group of a bilinear form `B`: linear automorphisms scaling `B`
by some unit `ν`, i.e. `B (g v₁) (g v₂) = ν * B v₁ v₂`. -/
def SimilitudeGroup (B : LinearMap.BilinForm k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {g | ∃ ν : kˣ, ∀ v₁ v₂, B (g v₁) (g v₂) = ν * B v₁ v₂}
  mul_mem' := by
    intro a b ⟨ν₁, hν₁⟩ ⟨ν₂, hν₂⟩
    exact ⟨ν₁ * ν₂, fun v₁ v₂ => by
      simp only [LinearEquiv.mul_apply, Units.val_mul]
      rw [hν₁ (b v₁) (b v₂), hν₂ v₁ v₂]; ring⟩
  one_mem' := ⟨1, fun v₁ v₂ => by simp⟩
  inv_mem' := by
    intro g ⟨ν, hν⟩
    exact ⟨ν⁻¹, fun v₁ v₂ => by
      have key := hν (g⁻¹ v₁) (g⁻¹ v₂)
      simp at key; rw [key]; simp⟩

/-- The orthogonal group of a symmetric bilinear form: the isometry group of `B`. -/
def OrthogonalGroup (B : LinearMap.BilinForm k V) (_hB : LinearMap.BilinForm.IsSymm B) :
    Subgroup (V ≃ₗ[k] V) :=
  IsometryGroup B

/-- The symplectic group of an alternating bilinear form: the isometry group of `B`. -/
def SymplecticGroup (B : LinearMap.BilinForm k V) (_hB : LinearMap.BilinForm.IsAlt B) :
    Subgroup (V ≃ₗ[k] V) :=
  IsometryGroup B

/-- The orthogonal similitude group: similitudes of a symmetric bilinear form. -/
def OrthogonalSimilitudeGroup (B : LinearMap.BilinForm k V)
    (_hB : LinearMap.BilinForm.IsSymm B) : Subgroup (V ≃ₗ[k] V) :=
  SimilitudeGroup B

/-- The symplectic similitude group: similitudes of an alternating bilinear form. -/
def SymplecticSimilitudeGroup (B : LinearMap.BilinForm k V)
    (_hB : LinearMap.BilinForm.IsAlt B) : Subgroup (V ≃ₗ[k] V) :=
  SimilitudeGroup B

end Garrett
