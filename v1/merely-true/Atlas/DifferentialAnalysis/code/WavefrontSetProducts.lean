/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory

namespace WavefrontSet

variable {n : ℕ}

/-- The zero tempered distribution has empty conic singular support: any `p` lies outside `Css 0`. -/
lemma not_mem_css_zero (p : ClosedBall n) :
    p ∉ Css (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, 0, by simp [map_zero]⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_, 0, by simp [map_zero]⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
        b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

/-- The Fourier transform of zero is zero, so its conic singular support is empty. -/
lemma not_mem_css_fourier_zero (q : ClosedBall n) :
    q ∉ Css (𝓕 (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))) := by
  have h0 : 𝓕 (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) = 0 := by ext g; simp
  rw [h0]
  exact not_mem_css_zero q


set_option maxHeartbeats 400000 in
/-- Subadditivity of the conic singular support: if `p ∉ Css u₁` and `p ∉ Css u₂`, then `p ∉ Css (u₁ + u₂)`. -/
theorem css_subadditive_not_mem
    {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p : ClosedBall n}
    (h₁ : p ∉ Css u₁) (h₂ : p ∉ Css u₂) :
    p ∉ Css (u₁ + u₂) := by
  simp only [Css, Set.mem_setOf] at h₁ h₂ ⊢
  split_ifs with h
  ·
    rw [dif_pos h] at h₁ h₂
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    obtain ⟨g₁, hg₁_conic, f₁, hf₁⟩ := h₁
    obtain ⟨g₂, hg₂_conic, f₂, hf₂⟩ := h₂

    refine ⟨g₁ * g₂, ?_, ?_⟩
    ·
      obtain ⟨hg₁_smooth, R₁, hR₁, hR₁_lt, R₀₁, hR₀₁, hg₁_supp, ψ₁, hψ₁_hom, hψ₁_ne, hg₁_eq⟩ := hg₁_conic
      obtain ⟨hg₂_smooth, R₂, hR₂, hR₂_lt, R₀₂, hR₀₂, hg₂_supp, ψ₂, hψ₂_hom, hψ₂_ne, hg₂_eq⟩ := hg₂_conic
      refine ⟨hg₁_smooth.mul hg₂_smooth, max R₁ R₂, lt_max_of_lt_left hR₁,
              max_lt hR₁_lt hR₂_lt,
              max R₀₁ R₀₂, lt_max_of_lt_left hR₀₁, ?_, ψ₁ * ψ₂, ?_, ?_, ?_⟩
      ·
        intro x hx
        simp only [Set.mem_setOf]
        rw [Function.mem_support, Pi.mul_apply] at hx
        have hx_ne : g₁ x ≠ 0 ∧ g₂ x ≠ 0 := mul_ne_zero_iff.mp hx
        have h1 : x ∈ Function.support g₁ := Function.mem_support.mpr hx_ne.1
        have h2 : x ∈ Function.support g₂ := Function.mem_support.mpr hx_ne.2
        exact max_le (hg₁_supp h1) (hg₂_supp h2)
      ·
        intro a ha x hx
        simp only [Pi.mul_apply]
        rw [hψ₁_hom a ha x hx, hψ₂_hom a ha x hx]
      ·
        simp only [Pi.mul_apply]
        exact mul_ne_zero hψ₁_ne hψ₂_ne
      ·
        intro x hx
        simp only [Pi.mul_apply]
        rw [hg₁_eq x (lt_of_le_of_lt (le_max_left _ _) hx),
            hg₂_eq x (lt_of_le_of_lt (le_max_right _ _) hx)]
    ·

      have hg₁_tg : Function.HasTemperateGrowth g₁ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₁ _ hg₁_conic
      have hg₂_tg : Function.HasTemperateGrowth g₂ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₂ _ hg₂_conic

      have eq1 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ =
          TemperedDistribution.smulLeftCLM ℂ g₂ (TemperedDistribution.smulLeftCLM ℂ g₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₁_tg hg₂_tg u₁).symm


      have mul_comm_g : g₂ * g₁ = g₁ * g₂ := mul_comm g₂ g₁
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ =
          TemperedDistribution.smulLeftCLM ℂ g₁ (TemperedDistribution.smulLeftCLM ℂ g₂ u₂) := by
        rw [← mul_comm_g]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₂_tg hg₁_tg u₂).symm

      rw [show TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) (u₁ + u₂) =
          TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ +
          TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ from
        map_add (TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂)) u₁ u₂]
      rw [eq1, hf₁, eq2, hf₂]

      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₂_tg f₁]

      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ g₂ f₁ + SchwartzMap.smulLeftCLM ℂ g₁ f₂,
             (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩
  ·
    rw [dif_neg h] at h₁ h₂
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h


    obtain ⟨φ₁, hφ₁_smooth, hφ₁_supp, hφ₁_ne, f₁, hf₁⟩ := h₁
    obtain ⟨φ₂, hφ₂_smooth, hφ₂_supp, hφ₂_ne, f₂, hf₂⟩ := h₂

    have hφ₁_tg : Function.HasTemperateGrowth φ₁ := hφ₁_supp.hasTemperateGrowth hφ₁_smooth
    have hφ₂_tg : Function.HasTemperateGrowth φ₂ := hφ₂_supp.hasTemperateGrowth hφ₂_smooth
    refine ⟨φ₁ * φ₂, hφ₁_smooth.mul hφ₂_smooth, hφ₁_supp.mul_right, ?_, ?_⟩
    ·
      simp only [Pi.mul_apply]
      exact mul_ne_zero hφ₁_ne hφ₂_ne
    ·
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₁ =
          TemperedDistribution.smulLeftCLM ℂ φ₂ (TemperedDistribution.smulLeftCLM ℂ φ₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₁_tg hφ₂_tg u₁).symm
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₂ =
          TemperedDistribution.smulLeftCLM ℂ φ₁ (TemperedDistribution.smulLeftCLM ℂ φ₂ u₂) := by
        rw [← mul_comm φ₂ φ₁]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₂_tg hφ₁_tg u₂).symm
      rw [ConeSupport.smulLeftCLM_add_right]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ φ₂ f₁ + SchwartzMap.smulLeftCLM ℂ φ₁ f₂,
             (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩










end WavefrontSet

end
