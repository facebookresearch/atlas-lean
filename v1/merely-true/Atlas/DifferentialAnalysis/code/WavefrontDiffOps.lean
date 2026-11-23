/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory ConeSupport

namespace WavefrontDiffOps

variable {n : ℕ}


/-- If a tempered distribution `u` is smooth near a point `x`, then the pair `(x, ω)` is not in
the wavefront set of `u` for any direction `ω`. -/
theorem not_mem_wavefrontSet_of_isSmoothNear
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (x : E n) (ω : Sphere n)
    (hsmooth : IsSmoothNear u x) :
    (x, ω) ∉ wavefrontSet u := by

  obtain ⟨φ, hφ_smooth, hφ_compact, hφx, f, hf⟩ := hsmooth


  intro hmem

  apply hmem
  refine ⟨φ, hφ_smooth, hφ_compact, hφx, ?_⟩


  rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]


  rw [schwartz_conicSingularSupportSphere_empty]
  simp




/-- For any open set `U` and point `x ∈ U`, there exists a smooth compactly supported complex
bump function `φ` with `φ x ≠ 0` and `tsupport φ ⊆ U`. -/
theorem exists_smooth_compactly_supported_in_open
    {n : ℕ} (U : Set (E n)) (hU : IsOpen U) (x : E n) (hx : x ∈ U) :
    ∃ (φ : E n → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ φ x ≠ 0 ∧
      tsupport φ ⊆ U := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU x hx
  have hr3 : (0 : ℝ) < r / 3 := by linarith
  have hr2 : r / 3 < r / 2 := by linarith
  set b : ContDiffBump x := ⟨r/3, r/2, hr3, hr2⟩
  refine ⟨fun y => Complex.ofReal (b y), ?_, ?_, ?_, ?_⟩
  · rw [contDiff_infty]; intro k
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  · simp only [Complex.ofReal_ne_zero]
    have h := b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt hr3))
    linarith
  · calc tsupport (fun y => (Complex.ofReal (b y) : ℂ))
        ⊆ tsupport b.toFun := tsupport_comp_subset Complex.ofReal_zero _
      _ = Metric.closedBall x (r/2) := b.tsupport_eq
      _ ⊆ Metric.ball x r := Metric.closedBall_subset_ball (by linarith)
      _ ⊆ U := hr_sub


/-- The projection to the base of the wavefront set is contained in the singular support. -/
theorem wavefrontSet_proj_fst_subset_singularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' wavefrontSet u ⊆ singularSupport u := by
  intro x ⟨⟨_, ω⟩, hxω_mem, rfl⟩
  intro hsmooth
  exact not_mem_wavefrontSet_of_isSmoothNear u x ω hsmooth hxω_mem



/-- The "boundary" subset of pairs `(p, q)` where at least one of the components corresponds to
a direction at infinity (an `Sum.inr` of `Sphere n`). -/
def boundaryOfProd : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  {p | (∃ ω : Sphere n, p.1 = Sum.inr ω) ∨ (∃ ω : Sphere n, p.2 = Sum.inr ω)}

/-- The scattering wavefront set is always contained in the boundary subset `boundaryOfProd`. -/
theorem scatteringWavefrontSet_subset_boundary
    (u : 𝓢'(E n, ℂ)) :
    scatteringWavefrontSet u ⊆ boundaryOfProd := by
  intro p hp
  simp only [scatteringWavefrontSet, Set.mem_union, Set.mem_image] at hp
  rcases hp with ⟨⟨x, ω⟩, _, rfl⟩ | ⟨⟨ω, q⟩, _, rfl⟩
  · right
    exact ⟨ω, rfl⟩
  · left
    exact ⟨ω, rfl⟩

/-- The wavefront set of a tempered distribution is a closed subset of `E n × Sphere n`. -/
theorem wavefrontSet_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (wavefrontSet u) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_forall_mem_open]
  intro ⟨x₀, ω₀⟩ h₀
  simp only [Set.mem_compl_iff] at h₀

  simp only [wavefrontSet, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀x₀, hω₀_notin⟩ := h₀

  refine ⟨(Function.support φ₀) ×ˢ
    (ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)))ᶜ,
    ?_, ?_, ?_⟩

  · intro ⟨x', ω'⟩ hx'ω'
    simp only [Set.mem_prod, Function.mem_support, Set.mem_compl_iff] at hx'ω'
    rw [Set.mem_compl_iff]
    simp only [wavefrontSet, Set.mem_setOf_eq, not_not]
    exact ⟨φ₀, hφ₀_smooth, hφ₀_compact, hx'ω'.1, hx'ω'.2⟩

  · exact IsOpen.prod (contDiff_isOpen_support φ₀ hφ₀_smooth)
      (cssSphere_isClosed _).isOpen_compl

  · exact Set.mk_mem_prod (Function.mem_support.mpr hφ₀x₀) hω₀_notin

/-- The singular support of a tempered distribution is closed in `E n`. -/
theorem singularSupport_isClosed {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (singularSupport u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x₀ h₀
  simp only [Set.mem_compl_iff, singularSupport, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀x₀, f₀, hf₀⟩ := h₀
  refine ⟨Function.support φ₀, ?_, contDiff_isOpen_support φ₀ hφ₀_smooth,
    Function.mem_support.mpr hφ₀x₀⟩
  intro x hx
  simp only [Set.mem_compl_iff, singularSupport, Set.mem_setOf_eq, not_not]
  exact ⟨φ₀, hφ₀_smooth, hφ₀_compact, Function.mem_support.mp hx, f₀, hf₀⟩

/-- The cone singular support of a tempered distribution is closed in `E n ⊕ Sphere n`. -/
theorem coneSingularSupport_isClosed {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (coneSingularSupport u) := by
  simp only [coneSingularSupport]
  apply IsClosed.union
  · exact Topology.IsClosedEmbedding.inl.isClosedMap _ (singularSupport_isClosed u)
  · exact Topology.IsClosedEmbedding.inr.isClosedMap _ (cssSphere_isClosed u)

/-- The set of sphere directions `ω` for which `g` is a conic cutoff near `ω` is open. -/
theorem isConicCutoffNear_isOpen {n : ℕ} (g : E n → ℂ) :
    IsOpen {ω : Sphere n | IsConicCutoffNear g ω} := by
  rw [isOpen_iff_forall_mem_open]
  intro ω₀ hω₀
  simp only [Set.mem_setOf_eq] at hω₀
  obtain ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hsupp, ψ, hψ_hom, hψ_ne, hψ_eq⟩ := hω₀

  refine ⟨{σ : Sphere n | ψ (σ : E n) ≠ 0}, ?_, ?_, hψ_ne⟩
  · intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ ⊢
    exact ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hsupp, ψ, hψ_hom, hσ, hψ_eq⟩
  ·


    set t := R + 1 with ht_def
    have ht_pos : (0 : ℝ) < t := by linarith
    have ht : R < t := by linarith

    have sphere_norm : ∀ (σ : Sphere n), ‖(σ : E n)‖ = 1 := by
      intro σ
      have hσ := σ.2
      simp only [Metric.mem_sphere, dist_zero_right] at hσ
      exact hσ
    have sphere_ne_zero : ∀ (σ : Sphere n), (σ : E n) ≠ 0 := by
      intro σ h
      have := sphere_norm σ
      rw [h, norm_zero] at this
      linarith
    have sphere_smul_norm : ∀ (σ : Sphere n), R < ‖t • (σ : E n)‖ := by
      intro σ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos, sphere_norm, mul_one]
      exact ht

    have key : ∀ (σ : Sphere n), ψ (σ : E n) = g (t • (σ : E n)) := by
      intro σ
      rw [← hψ_hom t ht_pos _ (sphere_ne_zero σ), hψ_eq _ (sphere_smul_norm σ)]

    have : {σ : Sphere n | ψ (σ : E n) ≠ 0} =
        (fun σ : Sphere n => g (t • (σ : E n))) ⁻¹' {0}ᶜ := by
      ext σ; simp [key]
    rw [this]
    exact (isClosed_singleton (X := ℂ)).isOpen_compl.preimage
      (hg_smooth.continuous.comp (continuous_const_smul t |>.comp continuous_subtype_val))

/-- The scattering wavefront set at infinity is a closed subset of `Sphere n × (E n ⊕ Sphere n)`. -/
theorem scatteringWavefrontSetAtInfinity_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (scatteringWavefrontSetAtInfinity u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ⟨ω₀, q₀⟩ h₀
  simp only [Set.mem_compl_iff, scatteringWavefrontSetAtInfinity, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨g₀, hg₀_conic, hq₀_notin⟩ := h₀
  refine ⟨{σ : Sphere n | IsConicCutoffNear g₀ σ} ×ˢ
    (coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)))ᶜ, ?_, ?_, ?_⟩
  · intro ⟨σ, q⟩ hσq
    simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_compl_iff] at hσq
    rw [Set.mem_compl_iff]
    simp only [scatteringWavefrontSetAtInfinity, Set.mem_setOf_eq, not_not]
    exact ⟨g₀, hσq.1, hσq.2⟩
  · exact IsOpen.prod (isConicCutoffNear_isOpen g₀) (coneSingularSupport_isClosed _).isOpen_compl
  · exact Set.mk_mem_prod hg₀_conic hq₀_notin

/-- The full scattering wavefront set (union of finite-part and at-infinity components) is closed. -/
theorem scatteringWavefrontSet_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (scatteringWavefrontSet u) := by
  simp only [scatteringWavefrontSet]
  apply IsClosed.union
  ·
    have hemb : Topology.IsClosedEmbedding
        (Prod.map (Sum.inl : E n → E n ⊕ Sphere n) (Sum.inr : Sphere n → E n ⊕ Sphere n)) := by
      constructor
      · exact Topology.IsEmbedding.prodMap
          Topology.IsClosedEmbedding.inl.isEmbedding
          Topology.IsClosedEmbedding.inr.isEmbedding
      · rw [Set.range_prodMap]
        exact isClosed_range_inl.prod isClosed_range_inr
    exact hemb.isClosedMap _ (wavefrontSet_isClosed u)
  ·
    have hemb : Topology.IsClosedEmbedding
        (Prod.map (Sum.inr : Sphere n → E n ⊕ Sphere n)
          (id : E n ⊕ Sphere n → E n ⊕ Sphere n)) := by
      constructor
      · exact Topology.IsEmbedding.prodMap
          Topology.IsClosedEmbedding.inr.isEmbedding
          Topology.IsClosedEmbedding.id.isEmbedding
      · rw [Set.range_prodMap]
        simp only [Set.range_id]
        exact isClosed_range_inr.prod isClosed_univ
    exact hemb.isClosedMap _ (scatteringWavefrontSetAtInfinity_isClosed u)


/-- If the first projection `p` is outside the cone singular support, then no pair `(p, q)`
belongs to the scattering wavefront set. -/
theorem not_mem_scatteringWavefrontSet_of_not_mem_coneSingularSupport
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (p : E n ⊕ Sphere n) (q : E n ⊕ Sphere n)
    (hp : p ∉ coneSingularSupport u) :
    (p, q) ∉ scatteringWavefrontSet u := by


  intro hmem
  simp only [scatteringWavefrontSet, Set.mem_union, Set.mem_image] at hmem
  rcases p with x | ω
  ·


    have hx_smooth : IsSmoothNear u x := by
      by_contra h_not_smooth
      apply hp
      exact Set.mem_union_left _ (Set.mem_image_of_mem Sum.inl h_not_smooth)
    rcases hmem with ⟨⟨x', ω'⟩, hxω, hprod⟩ | ⟨⟨ω', q'⟩, _, hprod⟩
    ·
      have hx_eq : x' = x := Sum.inl_injective (Prod.mk.inj hprod).1
      subst hx_eq
      exact not_mem_wavefrontSet_of_isSmoothNear u x' ω' hx_smooth hxω
    ·

      exact absurd (Prod.mk.inj hprod).1 Sum.inr_ne_inl
  ·


    have hω_not_css : ω ∉ ConicSingularSupportSphere u := by
      intro hω_css
      apply hp
      exact Set.mem_union_right _ (Set.mem_image_of_mem Sum.inr hω_css)

    simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_css
    obtain ⟨g, hg_conic, f, hf⟩ := hω_not_css
    rcases hmem with ⟨⟨x', ω'⟩, _, hprod⟩ | ⟨⟨ω', q'⟩, hωq, hprod⟩
    ·

      exact absurd (Prod.mk.inj hprod).1 Sum.inl_ne_inr
    ·
      have hω_eq : ω' = ω := Sum.inr_injective (Prod.mk.inj hprod).1
      have hq_eq : q' = q := (Prod.mk.inj hprod).2
      subst hω_eq; subst hq_eq


      apply hωq
      refine ⟨g, hg_conic, ?_⟩


      rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
      simp only [coneSingularSupport, schwartz_singularSupport_empty,
        schwartz_conicSingularSupportSphere_empty, Set.image_empty, Set.empty_union]
      exact Set.notMem_empty q'




/-- A tempered distribution is itself given by a Schwartz function whenever its Fourier transform
is. -/
theorem isSchwartz_of_fourier_isSchwartz
    {n : ℕ} (v : 𝓢'(E n, ℂ))
    (hv : ∃ (f : SchwartzMap (E n) ℂ), 𝓕 v = (f : 𝓢'(E n, ℂ))) :
    ∃ (f : SchwartzMap (E n) ℂ),
      v = (f : 𝓢'(E n, ℂ)) := by
  obtain ⟨f, hf⟩ := hv
  refine ⟨𝓕⁻ f, ?_⟩
  have h1 : 𝓕⁻ (f : 𝓢'(E n, ℂ)) = ((𝓕⁻ f : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ)) :=
    TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq f
  have h2 : 𝓕⁻ (𝓕 v) = v := FourierTransform.fourierInv_fourier_eq _
  rw [← h2, hf, h1]







/-- The projection to the first factor of the scattering wavefront set is contained in the cone
singular support. -/
theorem scatteringWavefrontSet_proj_fst_subset_coneSingularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' scatteringWavefrontSet u ⊆ coneSingularSupport u := by
  intro p ⟨⟨_, q⟩, hpq_mem, rfl⟩
  by_contra hp
  exact absurd hpq_mem
    (not_mem_scatteringWavefrontSet_of_not_mem_coneSingularSupport u p q hp)




end WavefrontDiffOps

end
