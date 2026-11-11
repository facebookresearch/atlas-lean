/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact

noncomputable section

open scoped SchwartzMap Pointwise
open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` on Euclidean space has compact support if there is a
compact `K` such that `u` annihilates every Schwartz function whose support is disjoint
from `K`. -/
def HasCompactSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ K = ∅) → u φ = 0

/-- If `μ` has compact support in the Schwartz-pairing sense, then its distributional
support `Distribution.dsupport μ` is compact. -/
theorem hasCompactDsupport_of_hasCompactSupport
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    HasCompactDsupport μ := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hμ

  have hclosed := Distribution.isClosed_dsupport (f := μ)

  have hK_closed : IsClosed K := hK_compact.isClosed
  have hvanish : Distribution.IsVanishingOn μ Kᶜ := by
    intro φ hφ
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have hy_tsupp : y ∈ tsupport (⇑φ) := subset_tsupport _ hy_supp
    exact absurd hy_K (Set.mem_compl_iff K y |>.mp (hφ hy_tsupp))
  have hsubset : Distribution.dsupport μ ⊆ K := by
    have hd := hvanish.disjoint_dsupport hK_closed.isOpen_compl
    rwa [Set.disjoint_compl_left_iff_subset] at hd
  exact hK_compact.of_isClosed_subset hclosed hsubset

/-- The reflection `φ ↦ φ ∘ (-id)` as a continuous linear endomorphism of the Schwartz
space `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def schwNegReflCLM :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)




/-- A decomposition of a tempered distribution `u = singular + smooth` into a singular
part with compact support contained in `supportSet` and a globally smooth, compactly
supported part. Used in the proof of `singularSupport_convolution_subset`. -/
structure SmoothDecomp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  singular : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  smooth : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  supportSet : Set (EuclideanSpace ℝ (Fin n))
  supportSet_compact : IsCompact supportSet
  singular_supported :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ supportSet = ∅) → singular φ = 0
  singular_compactSupport : HasCompactSupport singular
  smooth_isSmooth : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear smooth x₀
  smooth_compactSupport : HasCompactSupport smooth
  sum_eq : u = singular + smooth


/-- If `u` has compact support, then its singular support is compact (in particular,
closed and contained in the support of `u`). -/
theorem singularSupport_compact_of_compactSupport
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : HasCompactSupport u) :
    IsCompact (singularSupport u) := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  have hclosed : IsClosed (singularSupport u) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro x₀ hx₀
    have hsmooth : isSmoothNear u x₀ := not_not.mp hx₀
    obtain ⟨U, hU_open, hx₀_mem, f, hf_smooth, hf_eq⟩ := hsmooth
    refine ⟨U, fun x₁ hx₁ => ?_, hU_open, hx₀_mem⟩
    exact not_not.mpr ⟨U, hU_open, hx₁, f, hf_smooth, hf_eq⟩
  have hsubset : singularSupport u ⊆ K := by
    intro x₀ hx₀
    by_contra hx₀K
    apply hx₀
    have hK_closed : IsClosed K := hK_compact.isClosed
    refine ⟨Kᶜ, hK_closed.isOpen_compl, hx₀K, 0, contDiff_const, fun φ hφ => ?_⟩
    have hsup : Function.support (⇑φ) ∩ K = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      exact absurd (hφ y (not_not.mpr hy.2)) (mem_support.mp hy.1)
    rw [hK_supp φ hsup]
    simp [integral_zero]
  exact hK_compact.of_isClosed_subset hclosed hsubset


/-- Partition-of-unity identity for left multiplication by a tempered-growth function `χ`:
`χ · u + (1 - χ) · u = u`. -/
theorem smulLeft_add_complement
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : Function.HasTemperateGrowth χ := by fun_prop) :
    smulLeftCLM ℂ χ u + smulLeftCLM ℂ (1 - χ) u = u := by
  have h1χ : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ
  ext φ
  simp only [UniformConvergenceCLM.add_apply, smulLeftCLM_apply_apply]
  rw [← map_add u]
  congr 1
  ext x
  simp only [SchwartzMap.add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ, SchwartzMap.smulLeftCLM_apply_apply h1χ]
  simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]


/-- Multiplying a Schwartz function `φ` by a function `χ` (via `SchwartzMap.smulLeftCLM`)
can only shrink the support: `supp (χ · φ) ⊆ supp φ`. -/
lemma support_schwartz_smulLeft_subset
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Function.support (⇑(SchwartzMap.smulLeftCLM ℂ χ φ)) ⊆ Function.support (⇑φ) := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  unfold SchwartzMap.smulLeftCLM
  split
  · simp [SchwartzMap.bilinLeftCLM_apply, h]
  · simp


/-- If `u` has compact support, then so does the distribution `χ · u` obtained by left
multiplication by an arbitrary function `χ`. -/
theorem smulLeft_hasCompactSupport
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : HasCompactSupport u) :
    HasCompactSupport (smulLeftCLM ℂ χ u) := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  exact ⟨K, hK_compact, fun φ hφ => by
    simp only [smulLeftCLM_apply_apply]
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have : y ∈ Function.support (⇑φ) := support_schwartz_smulLeft_subset χ φ hy_supp
    exact Set.eq_empty_iff_forall_notMem.mp hφ y ⟨this, hy_K⟩⟩


/-- If the support of the cutoff function `χ` is contained in `S`, then the distribution
`χ · u` annihilates every Schwartz function whose support is disjoint from `S`. -/
theorem smulLeft_supported
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : tsupport χ ⊆ S) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ S = ∅) → (smulLeftCLM ℂ χ u) φ = 0 := by
  classical
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ χ φ = 0 by
    rw [h, map_zero]
  by_cases hg : HasTemperateGrowth χ
  · ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [SchwartzMap.coe_zero, Pi.zero_apply]
    by_cases hx : x ∈ support (⇑φ)
    · have hxS : x ∉ S := fun hxS =>
        (eq_empty_iff_forall_notMem.mp hφ) x ⟨hx, hxS⟩
      have hx_notin_supp : x ∉ support χ := fun h =>
        hxS (hS (subset_tsupport χ h))
      rw [notMem_support.mp hx_notin_supp, zero_smul]
    · rw [notMem_support.mp hx, smul_zero]
  · change (if hg : HasTemperateGrowth χ
        then SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip hg
        else 0) φ = 0
    rw [dif_neg hg]
    simp [ContinuousLinearMap.zero_apply]




set_option maxHeartbeats 400000 in
/-- Existence of a smooth complex-valued bump function which equals `1` on a neighbourhood
of a closed set `F` and is supported in a given compact superset `K` (with `F ⊆ int K`). -/
theorem exists_smooth_bump_subset
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hF : IsClosed F)
    (hK : IsCompact K)
    (hFK : F ⊆ interior K) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℂ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧
      _root_.HasCompactSupport χ ∧
      tsupport χ ⊆ K ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ F ⊆ V ∧ ∀ x ∈ V, χ x = 1) := by
  obtain ⟨f, hf_one, hf_zero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (n := ⊤) (s := F) (t := K) hF hFK
  let χ : EuclideanSpace ℝ (Fin n) → ℂ := fun x => ((f : EuclideanSpace ℝ (Fin n) → ℝ) x : ℂ)
  have hf_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
    contMDiff_iff_contDiff.mp f.2
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ :=
    Complex.ofRealCLM.contDiff.comp hf_contDiff
  have hsupp : Function.support (f : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h
    exact hx (hf_zero x h)
  have htsupp : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    rw [Function.mem_support] at hx
    have hxne : (f : EuclideanSpace ℝ (Fin n) → ℝ) x ≠ 0 := by
      intro heq; apply hx; simp [χ, heq]
    exact hsupp (Function.mem_support.mpr hxne)
  have hcompsupp : _root_.HasCompactSupport χ :=
    hK.of_isClosed_subset (isClosed_tsupport χ) htsupp
  refine ⟨χ, hsmooth, hcompsupp, htsupp, ?_⟩
  rw [eventually_nhdsSet_iff_forall] at hf_one
  refine ⟨interior {x | (f : EuclideanSpace ℝ (Fin n) → ℝ) x = 1}, isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hf_one x hx)
  · intro x hx
    have hfx := interior_subset hx
    simp only [χ, Set.mem_setOf_eq] at hfx ⊢
    rw [hfx, Complex.ofReal_one]
















/-- If a distribution `u` vanishes on an open neighbourhood `U` of `p`, then it is smooth
near `p` (with representative the zero function). -/
theorem isSmoothNear_of_vanishes_near
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hp : p ∈ U)
    (hv : vanishesOn u U) :
    isSmoothNear u p := by
  refine ⟨U, hU, hp, 0, contDiff_const, fun φ hφ => ?_⟩
  rw [hv φ hφ]
  simp [smul_zero, integral_zero]








/-- Tube-lemma–style enlargement: given compact `K₁, K₂` and a point `p` outside
`K₁ + K₂`, there exist compact `L₁, L₂` containing `K₁, K₂` in their interiors with
`p ∉ L₁ + L₂`. -/
theorem exists_compact_neighborhood_disjoint_sum
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin n)))
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (p : EuclideanSpace ℝ (Fin n))
    (hp : p ∉ K₁ + K₂) :
    ∃ (L₁ L₂ : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact L₁ ∧ IsCompact L₂ ∧ K₁ ⊆ interior L₁ ∧ K₂ ⊆ interior L₂ ∧ p ∉ L₁ + L₂ := by


  have hprod : K₁ ×ˢ K₂ ⊆ (fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ := by
    intro ⟨x, y⟩ ⟨hx, hy⟩ hmem
    apply hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact ⟨x, hx, y, hy, hmem⟩
  have hopen : IsOpen ((fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ) :=
    isOpen_compl_iff.mpr (isClosed_singleton.preimage (continuous_fst.add continuous_snd))

  obtain ⟨U₁, U₂, hU₁_open, hU₂_open, hK₁U₁, hK₂U₂, hprod_sub⟩ :=
    generalized_tube_lemma hK₁ hK₂ hopen hprod
  obtain ⟨L₁, hL₁_compact, hK₁_int, hL₁_sub⟩ := exists_compact_between hK₁ hU₁_open hK₁U₁
  obtain ⟨L₂, hL₂_compact, hK₂_int, hL₂_sub⟩ := exists_compact_between hK₂ hU₂_open hK₂U₂
  refine ⟨L₁, L₂, hL₁_compact, hL₂_compact, hK₁_int, hK₂_int, ?_⟩
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hab_mem : (a, b) ∈ U₁ ×ˢ U₂ := ⟨hL₁_sub ha, hL₂_sub hb⟩
  have := hprod_sub hab_mem
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at this
  exact this hab




/-- Multiplying a distribution `u` by a smooth function `χ` can only shrink the singular
support: `singsupp (χ · u) ⊆ singsupp u`. -/
theorem singularSupport_smulLeft_subset
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) :
    singularSupport (smulLeftCLM ℂ χ u) ⊆ singularSupport u := by
  classical
  by_cases htemp : Function.HasTemperateGrowth χ
  · exact singularSupport_smulLeft_subset_of_temperate χ hχ htemp u
  ·

    have hSchwartzZero : SchwartzMap.smulLeftCLM ℂ χ = (0 : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      split
      · exact absurd ‹_› htemp
      · rfl
    have hzero : smulLeftCLM ℂ χ u = 0 := by
      ext φ
      simp only [smulLeftCLM_apply_apply]
      rw [hSchwartzZero]
      simp
    intro x₀ hx₀
    exfalso
    apply hx₀
    rw [hzero]
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, contDiff_const, fun φ _ => ?_⟩
    simp [integral_zero]










end DifferentialOperators
