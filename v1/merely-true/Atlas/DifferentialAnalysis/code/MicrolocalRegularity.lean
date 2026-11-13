/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary

noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
sphere component `ConicSingularSupportSphere u` is also empty. -/
lemma ConicSingularSupportSphere_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.ConicSingularSupportSphere u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  have hp_norm : ‖w.val‖ = 1 := by
    have := w.property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hp_le : ‖w.val‖ ≤ 1 := le_of_eq hp_norm
  let p : ClosedBall n := ⟨w.val, hp_le⟩
  have hp_mem : p ∈ Css u := by
    show (if h : ‖p.val‖ = 1 then _ else _)
    rw [dif_pos hp_norm]
    convert hw using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
ordinary singular support is also empty. -/
lemma singularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.singularSupport u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have h1x_ne : (1 + ‖x‖ : ℝ) ≠ 0 := ne_of_gt h1x_pos
  set c := (1 + ‖x‖)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr h1x_pos
  have hc_norm : ‖c • x‖ = ‖x‖ / (1 + ‖x‖) := by
    rw [norm_smul, Real.norm_of_nonneg hc_pos.le, hc_def, inv_mul_eq_div]
  have hc_lt : ‖c • x‖ < 1 := by
    rw [hc_norm]
    rw [div_lt_one h1x_pos, lt_add_iff_pos_left]
    exact one_pos
  have hc_le : ‖c • x‖ ≤ 1 := le_of_lt hc_lt
  let p : ClosedBall n := ⟨c • x, hc_le⟩
  have hp_ne : ‖p.val‖ ≠ 1 := ne_of_lt hc_lt
  have hto : p.toEuclidean hc_lt = x := by
    simp only [ClosedBall.toEuclidean, p]
    rw [hc_norm]
    have h_factor : (1 : ℝ) - ‖x‖ / (1 + ‖x‖) = 1 / (1 + ‖x‖) := by
      field_simp
      ring
    rw [h_factor, one_div, inv_inv, smul_smul]
    rw [hc_def, mul_inv_cancel₀ h1x_ne, one_smul]
  have hp_mem : p ∈ Css u := by
    show (if hh : ‖p.val‖ = 1 then _ else _)
    rw [dif_neg hp_ne]
    convert hx using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
cone singular support (the union of singular support and conic sphere part) is also empty. -/
lemma coneSingularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.coneSingularSupport u = ∅ := by
  simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff, Set.image_eq_empty]
  exact ⟨singularSupport_empty_of_Css_empty u h,
    ConicSingularSupportSphere_empty_of_Css_empty u h⟩


/-- Predicate that `ψ₁` acts as a conic cutoff separating conic singular supports `K₁` and `K₂`:
multiplying by `ψ₁` (resp. `1 - ψ₁`) kills the conic singular support of any distribution whose
`Css` lies in `K₂` (resp. `K₁`). -/
structure IsConicCutoffForDisjointCss (K₁ K₂ : Set (ClosedBall n))
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop where
  schwartz_of_mul :
    ∀ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₂ ⊆ K₂ →
      Css (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂) = ∅
  schwartz_of_compl_mul :
    ∀ u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₁ ⊆ K₁ →
      Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) = ∅




/-- Partition of unity identity: for any temperate-growth `φ` and tempered distribution `u`, we have
`φ · u + (1 - φ) · u = u`. -/
theorem smul_partition
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ : φ.HasTemperateGrowth)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    TemperedDistribution.smulLeftCLM ℂ φ u +
      TemperedDistribution.smulLeftCLM ℂ (1 - φ) u = u := by
  have h1 : (1 : EuclideanSpace ℝ (Fin n) → ℂ).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const 1
  have h1φ : (1 - φ).HasTemperateGrowth := h1.sub hφ
  have hadd := TemperedDistribution.smulLeftCLM_add (F := ℂ) hφ h1φ
  have hone : φ + (1 - φ) = (1 : EuclideanSpace ℝ (Fin n) → ℂ) := by
    ext x; simp [Pi.add_apply, Pi.sub_apply]
  rw [hone] at hadd
  have key := congr_arg (· u) hadd.symm
  simp only [ContinuousLinearMap.add_apply] at key
  rw [key]
  have h_one_eq : (1 : EuclideanSpace ℝ (Fin n) → ℂ) = fun _ => (1 : ℂ) := rfl
  rw [h_one_eq, TemperedDistribution.smulLeftCLM_const, one_smul]


/-- The Schwartz embedding `schwEmbed : 𝓢(ℝⁿ, ℂ) → 𝓢'(ℝⁿ, ℂ)` is injective. -/
theorem schwEmbed_injective
    {n : ℕ}
    {f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
    (h : ConeSupport.schwEmbed f = ConeSupport.schwEmbed g) :
    f = g := by
  open MeasureTheory in
  rw [← sub_eq_zero]
  have hfg : ConeSupport.schwEmbed (f - g) = 0 := by
    simp only [map_sub, h, sub_self]
  apply SchwartzMap.injective_toLp (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) 2 (μ := volume)
  have hLp_eq : Lp.toTemperedDistribution ((f - g).toLp 2 volume) =
    (0 : TemperedDistribution (EuclideanSpace ℝ (Fin n)) ℂ) := by
    rw [Lp.toTemperedDistribution_toLp_eq]
    exact hfg
  have hinj := Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) (μ := volume) (p := 2)
  rw [LinearMap.ker_eq_bot'] at hinj
  exact hinj _ hLp_eq















/-- If multiplication by a temperate-growth `χ` fixes a tempered distribution `v`, then
multiplication by `1 - χ` annihilates `v`. -/
lemma smulLeft_complement_eq_zero_of_fixed
    {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hχ : χ.HasTemperateGrowth)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hfix : TemperedDistribution.smulLeftCLM ℂ χ v = v) :
    TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = 0 := by
  have hpart := smul_partition χ hχ v
  have : TemperedDistribution.smulLeftCLM ℂ χ v +
      TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = v := hpart
  rw [hfix] at this

  have := sub_eq_zero.mpr this
  simp only [add_sub_cancel_left] at this
  exact this





end WavefrontSet
