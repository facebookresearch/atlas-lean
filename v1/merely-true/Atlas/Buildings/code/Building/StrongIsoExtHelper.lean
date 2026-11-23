/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 400000













/-- Injectivity of $\delta$ in an apartment: assuming a Coxeter compatibility,
$\delta(C, D_1) = \delta(C, D_2)$ forces $D_1 = D_2$. -/
theorem delta_injective_in_apt_generic
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C D₁ D₂ : Finset V)
    (hC : A.IsMaximal C)
    (hD₁_mem : D₁ ∈ A.faces) (hD₁ : A.IsMaximal D₁)
    (hD₂_mem : D₂ ∈ A.faces) (hD₂ : A.IsMaximal D₂)
    (h_delta_compat : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
      (φ : Finset V → M.Group),
      (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
      ∃ (iso : W ≃* M.Group),
        ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
          iso (delta C D) = (φ C)⁻¹ * (φ D))
    (h_eq : delta C D₁ = delta C D₂) :
    D₁ = D₂ := by

  obtain ⟨B_idx, M, φ, hφ_inj, iso, h_compat⟩ := h_delta_compat

  have h1 : iso (delta C D₁) = iso (delta C D₂) := by rw [h_eq]

  rw [h_compat C D₁ hC.1 hC hD₁_mem hD₁,
      h_compat C D₂ hC.1 hC hD₂_mem hD₂] at h1


  have h2 : φ D₁ = φ D₂ := mul_left_cancel h1

  exact hφ_inj D₁ hD₁ D₂ hD₂ h2

