/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Atlas.DifferentialAnalysis.code.PseudoDiffOps
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization
import Mathlib.Algebra.Group.Pointwise.Set.Basic

noncomputable section

open scoped SchwartzMap FourierTransform Pointwise
open MeasureTheory

namespace ConeSupport

variable {n : ℕ}

/-- Two tempered distributions `u`, `v` admit an extended convolution as soon as at least one of
them has empty conic singular support on the sphere; this is the side condition under which
the convolution `u * v` can be defined microlocally. -/
def HasExtendedConvolution (u v : 𝓢'(E n, ℂ)) : Prop :=
  ConicSingularSupportSphere u = ∅ ∨ ConicSingularSupportSphere v = ∅




/-- The product of two conic cutoff functions near a direction `ω` is again a conic cutoff
near `ω`: the smoothness, support, and conic-extension properties are preserved by
multiplication. -/
lemma IsConicCutoffNear.mul {ga gb : E n → ℂ} {ω : Sphere n}
    (ha : IsConicCutoffNear ga ω) (hb : IsConicCutoffNear gb ω) :
    IsConicCutoffNear (ga * gb) ω := by
  obtain ⟨hga_smooth, Ra, hRa, hRa_lt, R0a, hR0a, hsupp_a, ψa, hψa_hom, hψa_ne, hga_eq⟩ := ha
  obtain ⟨hgb_smooth, Rb, hRb, hRb_lt, R0b, hR0b, hsupp_b, ψb, hψb_hom, hψb_ne, hgb_eq⟩ := hb
  refine ⟨hga_smooth.mul hgb_smooth, max Ra Rb, lt_max_of_lt_left hRa,
         max_lt hRa_lt hRb_lt,
         max R0a R0b, lt_max_of_lt_left hR0a, ?_, ψa * ψb, ?_, ?_, ?_⟩
  ·
    intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_ne : (ga * gb) x ≠ 0 := Function.mem_support.mp hx
    simp only [Pi.mul_apply] at hx_ne
    have hga_ne : ga x ≠ 0 := left_ne_zero_of_mul hx_ne
    have hgb_ne : gb x ≠ 0 := right_ne_zero_of_mul hx_ne
    have hRa_le := hsupp_a (Function.mem_support.mpr hga_ne)
    have hRb_le := hsupp_b (Function.mem_support.mpr hgb_ne)
    simp only [Set.mem_setOf_eq] at hRa_le hRb_le
    exact max_le hRa_le hRb_le
  ·
    intro c hc x hx
    simp [Pi.mul_apply, hψa_hom c hc x hx, hψb_hom c hc x hx]
  ·
    show ψa (ω : E n) * ψb (ω : E n) ≠ 0
    exact mul_ne_zero hψa_ne hψb_ne
  ·
    intro x hx
    simp only [Pi.mul_apply]
    have hRa' : Ra < ‖x‖ := lt_of_le_of_lt (le_max_left Ra Rb) hx
    have hRb' : Rb < ‖x‖ := lt_of_le_of_lt (le_max_right Ra Rb) hx
    rw [hga_eq x hRa', hgb_eq x hRb']

/-- Subadditivity of the conic singular support on the sphere under addition of distributions:
`ConicSingularSupportSphere (a + b) ⊆ ConicSingularSupportSphere a ∪ ConicSingularSupportSphere b`. -/
theorem ConicSingularSupportSphere_add_subset
    (a b : 𝓢'(E n, ℂ)) :
    ConicSingularSupportSphere (a + b) ⊆
      ConicSingularSupportSphere a ∪ ConicSingularSupportSphere b := by
  intro ω hω

  by_contra hω_not_union
  simp only [Set.mem_union, not_or] at hω_not_union
  obtain ⟨hω_not_a, hω_not_b⟩ := hω_not_union

  simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_a hω_not_b
  obtain ⟨ga, hga_conic, fa, hfa⟩ := hω_not_a
  obtain ⟨gb, hgb_conic, fb, hfb⟩ := hω_not_b


  apply hω


  by_cases hga_temp : Function.HasTemperateGrowth ga
  · by_cases hgb_temp : Function.HasTemperateGrowth gb
    ·

      have hprod_conic := hga_conic.mul hgb_conic


      have hcomp_a : TemperedDistribution.smulLeftCLM ℂ (ga * gb) a =
          TemperedDistribution.smulLeftCLM ℂ gb (TemperedDistribution.smulLeftCLM ℂ ga a) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hga_temp hgb_temp a).symm
      rw [hfa, smulLeftCLM_schwEmbed_eq gb fa] at hcomp_a


      have hcomm : (ga * gb : E n → ℂ) = gb * ga := mul_comm ga gb
      have hcomp_b : TemperedDistribution.smulLeftCLM ℂ (ga * gb) b =
          TemperedDistribution.smulLeftCLM ℂ ga (TemperedDistribution.smulLeftCLM ℂ gb b) := by
        rw [hcomm]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hgb_temp hga_temp b).symm
      rw [hfb, smulLeftCLM_schwEmbed_eq ga fb] at hcomp_b


      have hlin := map_add (TemperedDistribution.smulLeftCLM ℂ (ga * gb)) a b
      rw [hcomp_a, hcomp_b, ← map_add schwEmbed] at hlin
      exact ⟨ga * gb, hprod_conic,
        SchwartzMap.smulLeftCLM ℂ gb fa + SchwartzMap.smulLeftCLM ℂ ga fb, hlin⟩
    ·

      have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ gb = 0 := by
        unfold SchwartzMap.smulLeftCLM; exact dif_neg hgb_temp
      exact ⟨gb, hgb_conic, 0, by
        ext φ
        simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩
  ·
    have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ ga = 0 := by
      unfold SchwartzMap.smulLeftCLM; exact dif_neg hga_temp
    exact ⟨ga, hga_conic, 0, by
      ext φ
      simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩


/-- Subadditivity of the singular support under addition of tempered distributions:
`sing supp (a + b) ⊆ sing supp a ∪ sing supp b`. -/
theorem singularSupport_add_subset
    (a b : 𝓢'(E n, ℂ)) :
    singularSupport (a + b) ⊆ singularSupport a ∪ singularSupport b := by

  intro x hx
  by_contra h_not_mem

  have ha_not : x ∉ singularSupport a :=
    fun h => h_not_mem (Set.mem_union_left _ h)
  have hb_not : x ∉ singularSupport b :=
    fun h => h_not_mem (Set.mem_union_right _ h)

  have ha : IsSmoothNear a x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at ha_not
    exact ha_not
  have hb : IsSmoothNear b x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at hb_not
    exact hb_not

  obtain ⟨φ_a, hφa_smooth, hφa_compact, hφa_ne, f_a, hf_a⟩ := ha
  obtain ⟨φ_b, hφb_smooth, hφb_compact, hφb_ne, f_b, hf_b⟩ := hb

  have hφa_temp : φ_a.HasTemperateGrowth := hφa_compact.hasTemperateGrowth hφa_smooth
  have hφb_temp : φ_b.HasTemperateGrowth := hφb_compact.hasTemperateGrowth hφb_smooth

  have hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ_a * φ_b) :=
    hφa_smooth.mul hφb_smooth
  have hφ_compact : HasCompactSupport (φ_a * φ_b) := hφa_compact.mul_right
  have hφ_ne : (φ_a * φ_b) x ≠ 0 := mul_ne_zero hφa_ne hφb_ne

  have ha_eq : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
      TemperedDistribution.smulLeftCLM ℂ φ_b (TemperedDistribution.smulLeftCLM ℂ φ_a a) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφa_temp hφb_temp a).symm

  have ha_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a) := by
    rw [ha_eq, hf_a, smulLeftCLM_schwEmbed_eq]

  have hb_eq : TemperedDistribution.smulLeftCLM ℂ (φ_b * φ_a) b =
      TemperedDistribution.smulLeftCLM ℂ φ_a (TemperedDistribution.smulLeftCLM ℂ φ_b b) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφb_temp hφa_temp b).symm
  have hb_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) b =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [show φ_a * φ_b = φ_b * φ_a from mul_comm φ_a φ_b, hb_eq, hf_b, smulLeftCLM_schwEmbed_eq]

  have h_sum : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) (a + b) =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [map_add (TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b)) a b,
        ha_schwartz, hb_schwartz, map_add]

  have h_smooth : IsSmoothNear (a + b) x :=
    ⟨φ_a * φ_b, hφ_smooth, hφ_compact, hφ_ne,
     SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b, h_sum⟩

  exact absurd h_smooth (by rwa [singularSupport, Set.mem_setOf_eq] at hx)







/-- The two notions of "compactly supported distribution" used in the cone-support and
differential-operators namespaces coincide definitionally. -/
lemma isCompactlySupportedDistribution_iff_hasCompactSupport
    (w : 𝓢'(E n, ℂ)) :
    IsCompactlySupportedDistribution w ↔ DifferentialOperators.HasCompactSupport w :=
  Iff.rfl







/-- Singular support of the compact part of a Schwartz/compact decomposition is contained in
the singular support of the original distribution. -/
theorem singularSupport_compactPart_subset
    (u : 𝓢'(E n, ℂ))
    (d : SchwartzCompactDecomp u) :
    singularSupport d.compactPart ⊆ singularSupport u := by
  intro x hx
  rw [singularSupport, Set.mem_setOf_eq] at hx ⊢
  intro hu_smooth
  apply hx
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f_u, hf_u⟩ := hu_smooth
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
  have hg_eq : d.compactPart = u - schwEmbed d.schwartzPart :=
    eq_sub_of_add_eq' d.sum_eq.symm
  refine ⟨f_u - SchwartzMap.smulLeftCLM ℂ φ d.schwartzPart, ?_⟩
  rw [hg_eq, map_sub, hf_u, smulLeftCLM_schwEmbed_eq, map_sub]

























/-- Short-name alias for the subadditivity of `ConicSingularSupportSphere` under addition. -/
theorem cssSphere_add_subset
    (u₁ u₂ : 𝓢'(E n, ℂ)) :
    ConicSingularSupportSphere (u₁ + u₂) ⊆
      ConicSingularSupportSphere u₁ ∪ ConicSingularSupportSphere u₂ :=
  ConicSingularSupportSphere_add_subset u₁ u₂




end ConeSupport

end
