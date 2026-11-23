/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.Buildings.code.GeometricAlgebra.LagrangianFinrank
import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation

open FiniteDimensional Module Garrett

/-- Nondegeneracy of an orthogonal direct sum `B₁ ⊕ B₂` implies nondegeneracy
of the first summand `B₁`. -/
lemma nondeg_fst_of_orthogonalSum_nondeg
    {k : Type*} [Field k]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (h : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂)) :
    BilinForm.IsNondegenerate' B₁ := by
  rw [BilinForm.IsNondegenerate'] at h ⊢
  rw [Submodule.eq_bot_iff] at h ⊢
  intro v₁ hv₁
  have key : (v₁, (0 : V₂)) ∈ LinearMap.BilinForm.orthogonal
      (BilinForm.orthogonalSum B₁ B₂) ⊤ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro ⟨w₁, w₂⟩ _
    show (BilinForm.orthogonalSum B₁ B₂ ⟨w₁, w₂⟩) ⟨v₁, 0⟩ = 0
    simp only [BilinForm.orthogonalSum, LinearMap.mk₂_apply]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv₁
    have := hv₁ w₁ (Submodule.mem_top)
    unfold LinearMap.BilinForm.IsOrtho at this
    simp [this]
  have := h _ key
  exact Prod.mk.inj this |>.1
