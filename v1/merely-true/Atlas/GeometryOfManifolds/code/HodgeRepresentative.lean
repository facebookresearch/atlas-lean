/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

namespace HodgeRepresentative


/-- Abstract data for the Hodge-theoretic setting near degree $k+1$: three inner-product spaces
$\Omega^k, \Omega^{k+1}, \Omega^{k+2}$ with exterior derivatives $d_k, d_{k+1}$ satisfying
$d^2 = 0$ and their formal adjoints $d^*$. -/
structure HodgeData where
  Ωk : Type*
  Ωk1 : Type*
  Ωk2 : Type*
  [nacg_k : NormedAddCommGroup Ωk]
  [ips_k : InnerProductSpace ℝ Ωk]
  [nacg_k1 : NormedAddCommGroup Ωk1]
  [ips_k1 : InnerProductSpace ℝ Ωk1]
  [nacg_k2 : NormedAddCommGroup Ωk2]
  [ips_k2 : InnerProductSpace ℝ Ωk2]
  d_k : Ωk →ₗ[ℝ] Ωk1
  d_k1 : Ωk1 →ₗ[ℝ] Ωk2
  dstar_k1 : Ωk1 →ₗ[ℝ] Ωk
  dstar_k2 : Ωk2 →ₗ[ℝ] Ωk1
  d_squared : ∀ (α : Ωk), d_k1 (d_k α) = 0
  adjoint_d_k : ∀ (α : Ωk) (β : Ωk1),
    @inner ℝ Ωk1 _ (d_k α) β = @inner ℝ Ωk _ α (dstar_k1 β)
  adjoint_d_k1 : ∀ (α : Ωk1) (β : Ωk2),
    @inner ℝ Ωk2 _ (d_k1 α) β = @inner ℝ Ωk1 _ α (dstar_k2 β)

attribute [instance] HodgeData.nacg_k HodgeData.ips_k
  HodgeData.nacg_k1 HodgeData.ips_k1
  HodgeData.nacg_k2 HodgeData.ips_k2

variable (hd : HodgeData)


/-- The Hodge Laplacian $\Delta = d\,d^* + d^*\,d$ on $\Omega^{k+1}$. -/
noncomputable def HodgeData.laplacian (α : hd.Ωk1) : hd.Ωk1 :=
  hd.d_k (hd.dstar_k1 α) + hd.dstar_k2 (hd.d_k1 α)


/-- A form $\alpha$ is harmonic iff $\Delta \alpha = 0$. -/
def HodgeData.IsHarmonic (α : hd.Ωk1) : Prop :=
  hd.laplacian α = 0


/-- Existence data for the Hodge decomposition: a Green operator $G$ and harmonic projection $H$
such that $\alpha = H\alpha + d\,d^* G\alpha + d^* d\, G\alpha$, with $H\alpha$ harmonic,
closed, and co-closed. -/
structure HodgeData.GreenDecomp where
  G : hd.Ωk1 → hd.Ωk1
  H : hd.Ωk1 → hd.Ωk1
  H_harmonic : ∀ (α : hd.Ωk1), hd.IsHarmonic (H α)
  H_closed : ∀ (α : hd.Ωk1), hd.d_k1 (H α) = 0
  H_coclosed : ∀ (α : hd.Ωk1), hd.dstar_k1 (H α) = 0
  decomp : ∀ (α : hd.Ωk1),
    α = H α + hd.d_k (hd.dstar_k1 (G α)) + hd.dstar_k2 (hd.d_k1 (G α))


/-- A harmonic form that is also exact ($h = d\beta$) must be zero, by the orthogonality
$\langle d\beta, h\rangle = \langle \beta, d^* h\rangle = 0$. -/
lemma harmonic_exact_eq_zero
    (h : hd.Ωk1) (hH : hd.IsHarmonic h) (β : hd.Ωk) (heq : h = hd.d_k β) :
    h = 0 := by

  have hcoclosed : hd.dstar_k1 h = 0 := by
    unfold HodgeData.IsHarmonic HodgeData.laplacian at hH
    have key : @inner ℝ hd.Ωk1 _ (hd.d_k (hd.dstar_k1 h) + hd.dstar_k2 (hd.d_k1 h)) h
        = (0 : ℝ) := by
      rw [hH]; exact inner_zero_left (𝕜 := ℝ) h
    rw [inner_add_left] at key
    have h1 := hd.adjoint_d_k (hd.dstar_k1 h) h
    have h2 : @inner ℝ hd.Ωk1 _ (hd.dstar_k2 (hd.d_k1 h)) h =
        @inner ℝ hd.Ωk2 _ (hd.d_k1 h) (hd.d_k1 h) := by
      have := hd.adjoint_d_k1 h (hd.d_k1 h)
      rw [real_inner_comm] at this ⊢; exact this.symm
    rw [h1, h2] at key
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by
      linarith [real_inner_self_nonneg (x := hd.dstar_k1 h),
                real_inner_self_nonneg (x := hd.d_k1 h)])

  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (show @inner ℝ hd.Ωk1 _ h h = 0 from by
    calc @inner ℝ hd.Ωk1 _ h h
        = @inner ℝ hd.Ωk1 _ (hd.d_k β) h := by rw [heq]
      _ = @inner ℝ hd.Ωk _ β (hd.dstar_k1 h) := hd.adjoint_d_k β h
      _ = 0 := by rw [hcoclosed]; exact inner_zero_right (𝕜 := ℝ) β)


/-- The space of harmonic forms is closed under subtraction. -/
lemma harmonic_sub (h₁ h₂ : hd.Ωk1)
    (hH1 : hd.IsHarmonic h₁) (hH2 : hd.IsHarmonic h₂) :
    hd.IsHarmonic (h₁ - h₂) := by
  unfold HodgeData.IsHarmonic HodgeData.laplacian at *
  simp only [map_sub]
  calc hd.d_k (hd.dstar_k1 h₁) - hd.d_k (hd.dstar_k1 h₂) +
      (hd.dstar_k2 (hd.d_k1 h₁) - hd.dstar_k2 (hd.d_k1 h₂))
    = (hd.d_k (hd.dstar_k1 h₁) + hd.dstar_k2 (hd.d_k1 h₁)) -
      (hd.d_k (hd.dstar_k1 h₂) + hd.dstar_k2 (hd.d_k1 h₂)) := by abel
    _ = 0 - 0 := by rw [hH1, hH2]
    _ = 0 := sub_self 0


/-- Uniqueness helper: if $h_1 + d\beta_1 = h_2 + d\beta_2$ with both $h_i$ harmonic, then
$h_1 = h_2$ (since their difference is harmonic and exact). -/
lemma hodge_unique_helper
    (h₁ h₂ : hd.Ωk1) (β₁ β₂ : hd.Ωk)
    (hH1 : hd.IsHarmonic h₁) (hH2 : hd.IsHarmonic h₂)
    (heq : h₁ + hd.d_k β₁ = h₂ + hd.d_k β₂) :
    h₁ = h₂ := by
  have hdiff_harmonic := harmonic_sub hd h₁ h₂ hH1 hH2
  have hdiff_exact : h₁ - h₂ = hd.d_k (β₂ - β₁) := by
    have hsub : h₁ + hd.d_k β₁ - (h₂ + hd.d_k β₂) = 0 := sub_eq_zero.mpr heq
    simp only [map_sub]
    exact eq_of_sub_eq_zero (show h₁ - h₂ - (hd.d_k β₂ - hd.d_k β₁) = 0 from by
      calc h₁ - h₂ - (hd.d_k β₂ - hd.d_k β₁)
          = h₁ + hd.d_k β₁ - (h₂ + hd.d_k β₂) := by abel
        _ = 0 := hsub)
  exact sub_eq_zero.mp (harmonic_exact_eq_zero hd _ hdiff_harmonic _ hdiff_exact)


/-- Existence and uniqueness of the harmonic representative: every closed form $\alpha$
decomposes uniquely as $\alpha = h + d\beta$ with $h$ harmonic. -/
theorem hodge_representative_exists_unique
    (gd : hd.GreenDecomp)
    (α : hd.Ωk1) (hclosed : hd.d_k1 α = 0) :
    ∃! (h : hd.Ωk1), hd.IsHarmonic h ∧ ∃ (β : hd.Ωk), α = h + hd.d_k β := by


  have hdecomp := gd.decomp α

  have h_dstar_zero : hd.dstar_k2 (hd.d_k1 (gd.G α)) = 0 := by


    have h_Hclosed := gd.H_closed α
    have h_dsq := hd.d_squared (hd.dstar_k1 (gd.G α))
    have h_apply_d : hd.d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) = 0 := by
      have h_eq : hd.d_k1 α = hd.d_k1 (gd.H α) + hd.d_k1 (hd.d_k (hd.dstar_k1 (gd.G α)))
          + hd.d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) := by
        conv_lhs => rw [hdecomp]; simp [map_add]
      simp only [hclosed, h_Hclosed, h_dsq, zero_add] at h_eq; exact h_eq.symm

    have adj := hd.adjoint_d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) (hd.d_k1 (gd.G α))
    rw [h_apply_d, inner_zero_left (𝕜 := ℝ)] at adj
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp adj.symm

  have h_alpha_decomp : α = gd.H α + hd.d_k (hd.dstar_k1 (gd.G α)) := by
    have := hdecomp; rw [h_dstar_zero, add_zero] at this; exact this

  refine ⟨gd.H α, ⟨gd.H_harmonic α, hd.dstar_k1 (gd.G α), h_alpha_decomp⟩, ?_⟩
  intro h' ⟨hH', β', heq'⟩

  have h_eq : h' + hd.d_k β' = gd.H α + hd.d_k (hd.dstar_k1 (gd.G α)) := by
    rw [← heq', ← h_alpha_decomp]
  exact hodge_unique_helper hd h' (gd.H α) β' (hd.dstar_k1 (gd.G α))
    hH' (gd.H_harmonic α) h_eq

end HodgeRepresentative
