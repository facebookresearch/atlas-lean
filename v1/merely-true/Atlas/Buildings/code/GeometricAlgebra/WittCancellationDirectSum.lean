/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.RelClasses

set_option maxHeartbeats 2000000

namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- `φ : V₁ ≃ₗ V₂` is an isometry of formed spaces with respect to `B₁` and `B₂`
if it preserves the bilinear forms. -/
def IsFormedSpaceIso
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (φ : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ v w : V₁, B₂ (φ v) (φ w) = B₁ v w

/-- Orthogonal direct sum of two bilinear forms `B_U` on `U` and `B_W` on `W`. -/
def orthogonalSumForm
    {U W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (B_U : LinearMap.BilinForm k U) (B_W : LinearMap.BilinForm k W) :
    LinearMap.BilinForm k (U × W) :=
  LinearMap.mk₂ k
    (fun x y => B_U x.1 y.1 + B_W x.2 y.2)
    (fun x₁ x₂ y => by simp [map_add]; ring)
    (fun c x y => by simp [map_smul]; ring)
    (fun x y₁ y₂ => by simp [map_add]; ring)
    (fun c x y => by simp [map_smul]; ring)

/-- Evaluation formula for the orthogonal direct sum bilinear form. -/
@[simp]
lemma orthogonalSumForm_apply
    {U W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (B_U : LinearMap.BilinForm k U) (B_W : LinearMap.BilinForm k W)
    (x y : U × W) :
    orthogonalSumForm B_U B_W x y = B_U x.1 y.1 + B_W x.2 y.2 := by
  simp [orthogonalSumForm, LinearMap.mk₂]

/-- A bilinear form is nondegenerate (in the orthogonal-complement sense) if
the orthogonal complement of the whole space is trivial. -/
def IsNondegenerate'
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥

/-- A bilinear form is symmetric: `B x y = B y x` for all `x, y`. -/
def IsSymmetric'
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  ∀ x y : V, B x y = B y x




/-- If `Ψ` is an isometry of `U ⊕ V` and `U ⊕ W` fixing the `U`-summand, then the
first component of `Ψ (0, v)` vanishes for every `v ∈ V`. -/
lemma first_component_zero
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B_U : LinearMap.BilinForm k U)
    (B_V : LinearMap.BilinForm k V)
    (B_W : LinearMap.BilinForm k W)
    (hU_nd : IsNondegenerate' B_U)
    (Ψ : (U × V) ≃ₗ[k] (U × W))
    (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
    (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0))
    (v : V) : (Ψ (0, v)).1 = 0 := by


  have h_ortho : ∀ u : U, B_U u (Ψ (0, v)).1 = 0 := by
    intro u
    have key := hΨ (u, 0) (0, v)
    simp [orthogonalSumForm_apply] at key
    rw [hΨ_U] at key; simp at key; exact key

  have h_mem : (Ψ (0, v)).1 ∈ LinearMap.BilinForm.orthogonal B_U ⊤ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro x _; exact h_ortho x
  rw [hU_nd] at h_mem; exact h_mem


/-- Extract a linear equivalence `V ≃ₗ W` from a `U`-fixing isometry `Ψ` of
`U ⊕ V` and `U ⊕ W`, by sending `v` to the second component of `Ψ (0, v)`. -/
noncomputable def extractEquiv
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B_U : LinearMap.BilinForm k U) (B_V : LinearMap.BilinForm k V)
    (B_W : LinearMap.BilinForm k W)
    (hU_nd : IsNondegenerate' B_U)
    (Ψ : (U × V) ≃ₗ[k] (U × W))
    (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
    (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0)) :
    V ≃ₗ[k] W := by

  let f : V →ₗ[k] W :=
    { toFun := fun v => (Ψ (0, v)).2
      map_add' := fun v₁ v₂ => by
        have h := congr_arg Prod.snd (Ψ.map_add (0, v₁) (0, v₂))
        simp at h; exact h
      map_smul' := fun c v => by
        have h := congr_arg Prod.snd (Ψ.map_smul c (0, v))
        simp at h; exact h }


  have hf_inj : Function.Injective f := by
    intro v₁ v₂ hfv
    have hfst := first_component_zero B_U B_V B_W hU_nd Ψ hΨ hΨ_U
    have h1 : Ψ (0, v₁) = Ψ (0, v₂) := by
      ext
      · rw [hfst v₁, hfst v₂]
      · exact hfv
    exact Prod.ext_iff.mp (Ψ.injective h1) |>.2


  have hf_surj : Function.Surjective f := by
    have hdim : Module.finrank k V = Module.finrank k W := by
      have h1 : Module.finrank k (U × V) = Module.finrank k U + Module.finrank k V :=
        Module.finrank_prod
      have h2 : Module.finrank k (U × W) = Module.finrank k U + Module.finrank k W :=
        Module.finrank_prod
      linarith [LinearEquiv.finrank_eq Ψ]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  exact LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- The extracted linear equivalence `V ≃ₗ W` is an isometry of the formed
spaces `(V, B_V)` and `(W, B_W)`. -/
lemma extractEquiv_isometry
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B_U : LinearMap.BilinForm k U) (B_V : LinearMap.BilinForm k V)
    (B_W : LinearMap.BilinForm k W)
    (hU_nd : IsNondegenerate' B_U)
    (Ψ : (U × V) ≃ₗ[k] (U × W))
    (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
    (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0)) :
    IsFormedSpaceIso B_V B_W (extractEquiv B_U B_V B_W hU_nd Ψ hΨ hΨ_U) := by
  intro v₁ v₂

  show B_W (Ψ (0, v₁)).2 (Ψ (0, v₂)).2 = B_V v₁ v₂
  have hfst := first_component_zero B_U B_V B_W hU_nd Ψ hΨ hΨ_U

  have key := hΨ (0, v₁) (0, v₂)
  simp [orthogonalSumForm_apply] at key

  rw [hfst v₁, hfst v₂] at key
  simp at key
  exact key



end Garrett
