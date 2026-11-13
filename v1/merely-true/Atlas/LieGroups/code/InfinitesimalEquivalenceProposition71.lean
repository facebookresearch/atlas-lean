/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.InfinitesimalEquivalenceCore

noncomputable section

theorem norm_of_inner_preserving
    {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
    (S₁ : Submodule ℂ V₁) (S₂ : Submodule ℂ V₂)
    (A : S₁ ≃ₗ[ℂ] S₂)
    (h_inner : ∀ (x y : S₁),
      @inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A y)) =
      @inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype y)) :
    ∀ x : S₁, ‖S₂.subtype (A x)‖ = ‖S₁.subtype x‖ := by
  intro x
  have h := h_inner x x
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₂.subtype (A x))
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₁.subtype x)
  have h3 : RCLike.re (@inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A x))) =
    RCLike.re (@inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype x)) := by rw [h]
  rw [h1, h2] at h3
  have ha : (0 : ℝ) ≤ ‖S₂.subtype (A x)‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖S₁.subtype x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖S₂.subtype (A x)‖ - ‖S₁.subtype x‖)]









theorem equivariance_extends_from_dense
    {G : Type*} [Group G] [TopologicalSpace G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (T : F₁ ≃ₗᵢ[ℂ] F₂)
    {S : Type*} [TopologicalSpace S]
    (ι : S → F₁) (h_dense : DenseRange ι)
    (h_agree : ∀ (g : G) (s : S),
      T (π₁.toMonoidHom g (ι s)) = π₂.toMonoidHom g (T (ι s))) :
    ∀ (g : G) (v : F₁),
      T (π₁.toMonoidHom g v) = π₂.toMonoidHom g (T v) := by
  intro g
  have hT_cont : Continuous T := T.continuous
  have hπ₁g_cont : Continuous (π₁.toMonoidHom g) := (π₁.toMonoidHom g).continuous
  have hπ₂g_cont : Continuous (π₂.toMonoidHom g) := (π₂.toMonoidHom g).continuous
  have h_lhs_cont : Continuous (fun v => T (π₁.toMonoidHom g v)) :=
    hT_cont.comp hπ₁g_cont
  have h_rhs_cont : Continuous (fun v => π₂.toMonoidHom g (T v)) :=
    hπ₂g_cont.comp hT_cont
  have h_eq_on_dense :
      (fun v => T (π₁.toMonoidHom g v)) ∘ ι =
      (fun v => π₂.toMonoidHom g (T v)) ∘ ι :=
    funext (fun s => h_agree g s)
  exact fun v => congr_fun
    (DenseRange.equalizer h_dense h_lhs_cont h_rhs_cont h_eq_on_dense) v


end
