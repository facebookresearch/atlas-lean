/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.SchwartzSingularSupport
import Atlas.DifferentialAnalysis.code.SmoothPartitionOfUnity

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}


/-- Multiplication by `φ` commutes with the Schwartz embedding: the tempered distribution obtained
by applying `smulLeftCLM` to the Schwartz embedding of `f` equals the Schwartz embedding of
`φ · f`. -/
lemma smulLeftCLM_schwEmbed_eq
    (φ : E n → ℂ) (f : 𝓢(E n, ℂ)) :
    TemperedDistribution.smulLeftCLM ℂ φ (schwEmbed f) =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ f) := by
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1
  ext x
  by_cases hφ : Function.HasTemperateGrowth φ
  · simp only [SchwartzMap.smulLeftCLM_apply_apply hφ, smul_eq_mul]
    ring
  · have : SchwartzMap.smulLeftCLM ℂ φ = (0 : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      exact dif_neg hφ
    simp [this]


/-- If `u = schwEmbed f + g` and `u` has empty singular support, then the compactly supported part
`g` also has empty singular support. -/
lemma singularSupport_compactPart_empty_of_decomp
    {u : 𝓢'(E n, ℂ)}
    (hsing : singularSupport u = ∅)
    (f : 𝓢(E n, ℂ))
    (g : 𝓢'(E n, ℂ))
    (hdecomp : u = schwEmbed f + g) :
    singularSupport g = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [singularSupport, Set.mem_setOf_eq] at hx
  have hu_smooth : IsSmoothNear u x := by
    rw [Set.eq_empty_iff_forall_notMem] at hsing
    exact not_not.mp (hsing x)
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f_u, hf_u⟩ := hu_smooth
  apply hx
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
  have hg_eq : g = u - schwEmbed f := by
    rw [hdecomp]; abel
  refine ⟨f_u - SchwartzMap.smulLeftCLM ℂ φ f, ?_⟩
  rw [hg_eq, map_sub, hf_u, smulLeftCLM_schwEmbed_eq, map_sub]



/-- Associativity of left multiplication on tempered distributions: applying `smulLeftCLM a` after
`smulLeftCLM b` equals `smulLeftCLM (a * b)`. -/
lemma smulLeftCLM_comp_eq_mul
    (a b : E n → ℂ) (u : 𝓢'(E n, ℂ))
    (ha : Function.HasTemperateGrowth a)
    (hb : Function.HasTemperateGrowth b)
    (hab : Function.HasTemperateGrowth (a * b)) :
    TemperedDistribution.smulLeftCLM ℂ a (TemperedDistribution.smulLeftCLM ℂ b u) =
    TemperedDistribution.smulLeftCLM ℂ (a * b) u := by
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply ha, SchwartzMap.smulLeftCLM_apply_apply hb,
    SchwartzMap.smulLeftCLM_apply_apply hab, smul_eq_mul, Pi.mul_apply]
  ring

/-- If a smooth, compactly supported, temperate-growth function `φ` equals `1` on a compact set `K`
containing the support of the distribution `g`, then multiplication by `φ` fixes `g`. -/
lemma smulLeftCLM_eq_self_of_one_on_support
    (g : 𝓢'(E n, ℂ))
    (K : Set (E n)) (_hK : IsCompact K)
    (hK_supp : ∀ f : 𝓢(E n, ℂ), (Function.support (⇑f) ∩ K = ∅) → g f = 0)
    (φ : E n → ℂ)
    (_hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (_hφ_compact : HasCompactSupport φ)
    (hφ_one : ∀ x ∈ K, φ x = 1)
    (hφ_tg : Function.HasTemperateGrowth φ) :
    TemperedDistribution.smulLeftCLM ℂ φ g = g := by
  have h1mφ_tg : Function.HasTemperateGrowth (1 - φ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hφ_tg
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  have key : ψ = SchwartzMap.smulLeftCLM ℂ φ ψ +
      SchwartzMap.smulLeftCLM ℂ (1 - φ) ψ := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply hφ_tg,
      SchwartzMap.smulLeftCLM_apply_apply h1mφ_tg, smul_eq_mul,
      SchwartzMap.add_apply, Pi.sub_apply, Pi.one_apply]
    ring
  conv_rhs => rw [key, map_add]
  have hzero : g (SchwartzMap.smulLeftCLM ℂ (1 - φ) ψ) = 0 := by
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro x ⟨hx_supp, hx_K⟩
    rw [Function.mem_support] at hx_supp
    simp only [SchwartzMap.smulLeftCLM_apply_apply h1mφ_tg, smul_eq_mul,
      Pi.sub_apply, Pi.one_apply] at hx_supp
    have := hφ_one x hx_K
    simp [this] at hx_supp
  rw [hzero, add_zero]

/-- If `ψ · g` is given by a Schwartz function and the support of the smooth compactly supported
`φ` lies inside the non-vanishing set of `ψ`, then `φ · g` is also given by a Schwartz function. -/
lemma smulLeftCLM_schwartz_of_supported_in_smooth
    (g : 𝓢'(E n, ℂ))
    (φ : E n → ℂ)
    (hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (ψ : E n → ℂ)
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (h_supp : tsupport φ ⊆ {y | ψ y ≠ 0})
    (f : SchwartzMap (E n) ℂ)
    (hf : TemperedDistribution.smulLeftCLM ℂ ψ g = schwEmbed f) :
    ∃ (s : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ g = schwEmbed s := by

  let θ : E n → ℂ := fun y => φ y / ψ y

  have hθ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    ·
      show ContDiffAt ℝ _ (fun y => φ y * (ψ y)⁻¹) x
      exact hφ_smooth.contDiffAt.mul (hψ_smooth.contDiffAt.inv (h_supp hx))
    ·
      have hθ_zero : θ =ᶠ[nhds x] 0 := by
        have hmem : (tsupport φ)ᶜ ∈ nhds x := by
          exact isOpen_compl_iff.mpr (isClosed_tsupport (f := φ)) |>.mem_nhds hx
        filter_upwards [hmem] with y hy
        show φ y / ψ y = 0
        have : y ∉ Function.support φ := fun h => hy (subset_tsupport _ h)
        simp [Function.notMem_support.mp this]
      rw [show (0 : E n → ℂ) = fun _ => (0 : ℂ) from rfl] at hθ_zero
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hθ_zero
  have hθ_compact : HasCompactSupport θ := by
    apply HasCompactSupport.of_support_subset_isCompact hφ_compact
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport φ (Function.mem_support.mpr (fun h => by simp [θ, h] at hx))

  have hθ_tg : Function.HasTemperateGrowth θ := hθ_compact.hasTemperateGrowth hθ_smooth
  have hψ_tg : Function.HasTemperateGrowth ψ := hψ_compact.hasTemperateGrowth hψ_smooth

  have hθψ : θ * ψ = φ := by
    ext y
    simp only [θ, Pi.mul_apply]
    by_cases h : ψ y = 0
    · have : y ∉ tsupport φ := fun hy => (h_supp hy) h
      have : y ∉ Function.support φ := fun hy => this (subset_tsupport _ hy)
      simp [Function.notMem_support.mp this, h]
    · exact div_mul_cancel₀ (φ y) h

  have hθψ_tg : Function.HasTemperateGrowth (θ * ψ) := by
    rw [hθψ]; exact hφ_compact.hasTemperateGrowth hφ_smooth

  have hassoc := smulLeftCLM_comp_eq_mul θ ψ g hθ_tg hψ_tg hθψ_tg

  rw [hf] at hassoc

  rw [smulLeftCLM_schwEmbed_eq] at hassoc

  rw [hθψ] at hassoc
  exact ⟨SchwartzMap.smulLeftCLM ℂ θ f, hassoc.symm⟩


/-- If `g` has empty singular support, then multiplying it by any smooth compactly supported `φ`
yields a tempered distribution that is the Schwartz embedding of a Schwartz function. -/
theorem smulLeftCLM_schwartz_of_emptySingSupp
    (g : 𝓢'(E n, ℂ))
    (hsing : singularSupport g = ∅)
    (φ : E n → ℂ)
    (hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (_hφ_tg : Function.HasTemperateGrowth φ) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ g = schwEmbed f := by

  have hsmooth : ∀ x : E n, IsSmoothNear g x := by
    intro x
    rw [Set.eq_empty_iff_forall_notMem] at hsing
    exact not_not.mp (hsing x)

  choose ψ hψS hψC hψN fW hfW using fun x => hsmooth x

  have hU_open : ∀ x, IsOpen {y | ψ x y ≠ 0} :=
    fun x => (hψS x).continuous.isOpen_preimage _ isOpen_compl_singleton
  have hU_cover : tsupport φ ⊆ ⋃ x, {y | ψ x y ≠ 0} :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hψN y⟩

  obtain ⟨N, ηR, aI, hηS, _, _, hηT, V, _, hVK, hηSum⟩ :=
    SmoothPartitionOfUnity.exists_smooth_finitePartition_of_isCompact
      hU_open hφ_compact hU_cover


  set φ_i : Fin N → E n → ℂ := fun i y => (Complex.ofRealCLM (ηR i y)) * φ y
  have hφi_smooth : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ_i i) := by
    intro i
    exact (Complex.ofRealCLM.contDiff.comp (hηS i)).mul hφ_smooth
  have hφi_compact : ∀ i, HasCompactSupport (φ_i i) := by
    intro i
    apply HasCompactSupport.of_support_subset_isCompact hφ_compact
    intro x hx
    rw [Function.mem_support] at hx
    simp only [φ_i, Complex.ofRealCLM_apply, mul_ne_zero_iff] at hx
    exact subset_tsupport _ (Function.mem_support.mpr hx.2)
  have hφi_supp : ∀ i, tsupport (φ_i i) ⊆ {y | ψ (aI i) y ≠ 0} := by
    intro i


    apply subset_trans _ (hηT i)
    apply closure_mono
    intro y hy
    rw [Function.mem_support] at hy ⊢
    simp only [φ_i, Complex.ofRealCLM_apply, mul_ne_zero_iff] at hy
    exact_mod_cast hy.1


  have hpiece : ∀ i, ∃ s : 𝓢(E n, ℂ),
      TemperedDistribution.smulLeftCLM ℂ (φ_i i) g = schwEmbed s :=
    fun i => smulLeftCLM_schwartz_of_supported_in_smooth g (φ_i i)
      (hφi_smooth i) (hφi_compact i) (ψ (aI i)) (hψS (aI i)) (hψC (aI i))
      (hφi_supp i) (fW (aI i)) (hfW (aI i))

  have hφ_eq : φ = ∑ i, φ_i i := by
    ext y
    simp only [φ_i, Complex.ofRealCLM_apply, Finset.sum_apply]
    by_cases hy : y ∈ tsupport φ
    · rw [← Finset.sum_mul]
      have h1 := hηSum y (hVK hy)
      rw [show (∑ i : Fin N, ↑(ηR i y)) = (↑(∑ i : Fin N, ηR i y) : ℂ) from by push_cast; rfl,
        show (↑(∑ i : Fin N, ηR i y) : ℂ) = 1 from by exact_mod_cast h1, one_mul]
    · have hφ_zero : φ y = 0 := by
        exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
      simp [hφ_zero]

  choose s hs using hpiece
  refine ⟨∑ i, s i, ?_⟩
  rw [map_sum]

  have hlin : TemperedDistribution.smulLeftCLM ℂ φ g =
      ∑ i, TemperedDistribution.smulLeftCLM ℂ (φ_i i) g := by
    have hφi_tg : ∀ j, Function.HasTemperateGrowth (φ_i j) :=
      fun j => (hφi_compact j).hasTemperateGrowth (hφi_smooth j)
    ext ψ₀


    conv_lhs => rw [hφ_eq]
    have hsum_tg : Function.HasTemperateGrowth (∑ j : Fin N, φ_i j) := by
      rw [← hφ_eq]; exact hφ_compact.hasTemperateGrowth hφ_smooth


    simp only [TemperedDistribution.smulLeftCLM_apply_apply]


    rw [show (∑ i, (TemperedDistribution.smulLeftCLM ℂ (φ_i i)) g) ψ₀ =
        ∑ i, g ((SchwartzMap.smulLeftCLM ℂ (φ_i i)) ψ₀) from by
      simp [TemperedDistribution.smulLeftCLM_apply_apply]]
    rw [← map_sum g]
    congr 1
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply hsum_tg, smul_eq_mul]
    simp [SchwartzMap.smulLeftCLM_apply_apply (hφi_tg _), smul_eq_mul, Finset.sum_mul]
  rw [hlin]
  congr 1
  funext i
  exact hs i


/-- If the Schwartz embedding of `f` is supported (as a distribution) inside a compact set `K`,
then the function support of `f` is contained in `K`. -/
theorem schwEmbed_compact_support_of_distrib_compact_support
    (f : 𝓢(E n, ℂ))
    (K : Set (E n)) (hK : IsCompact K)
    (hK_supp : ∀ ψ : 𝓢(E n, ℂ), (Function.support (⇑ψ) ∩ K = ∅) →
      (schwEmbed f) ψ = 0) :
    Function.support (⇑f) ⊆ K := by

  rw [Function.support_subset_iff']
  intro x hx

  have hKc_open : IsOpen (Kᶜ) := hK.isClosed.isOpen_compl

  have hf_cont : Continuous (⇑f) := (f : SchwartzMap (E n) ℂ).continuous

  have hf_li : LocallyIntegrableOn (⇑f) Kᶜ :=
    (hf_cont.locallyIntegrable).locallyIntegrableOn Kᶜ


  have hint_zero : ∀ (g : E n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Kᶜ → ∫ x, g x • f x ∂volume = 0 := by
    intro g hg_smooth hg_compact hg_tsupport

    have hg_c_compact : HasCompactSupport (Complex.ofReal ∘ g) :=
      hg_compact.comp_left Complex.ofReal_zero
    have hg_c_smooth : ContDiff ℝ ∞ (Complex.ofReal ∘ g) :=
      (Complex.ofRealCLM.contDiff (n := ∞)).comp hg_smooth
    let ψ : 𝓢(E n, ℂ) := hg_c_compact.toSchwartzMap hg_c_smooth


    have hψ_supp : Function.support (⇑ψ) ∩ K = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y ⟨hy_supp, hy_K⟩
      rw [Function.mem_support] at hy_supp
      simp only [ψ, HasCompactSupport.toSchwartzMap_toFun] at hy_supp
      have hgy : g y ≠ 0 := by
        intro hg0; exact hy_supp (by simp [hg0])
      have : y ∈ Function.support g := Function.mem_support.mpr hgy
      have : y ∈ tsupport g := subset_closure this
      exact absurd (hg_tsupport this) (Set.notMem_compl_iff.mpr hy_K)


    have := hK_supp ψ hψ_supp

    simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply] at this


    convert this using 1

  have hae : ∀ᵐ y, y ∈ Kᶜ → (f : E n → ℂ) y = 0 :=
    hKc_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf_li hint_zero

  have h_eq : ∀ y ∈ Kᶜ, (f : E n → ℂ) y = 0 := by
    have hae' : (⇑f) =ᵐ[volume.restrict Kᶜ] 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hKc_open.measurableSet]
      filter_upwards [hae] with y hy hy_mem
      exact hy hy_mem
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hKc_open
      hf_cont.continuousOn continuousOn_const
  exact h_eq x hx


/-- A compactly supported distribution with empty singular support is represented by integration
against a smooth, compactly supported function. -/
theorem compactlySupported_emptySingSupp_represented_by_smooth
    (g : 𝓢'(E n, ℂ))
    (hcomp : IsCompactlySupportedDistribution g)
    (hsing : singularSupport g = ∅) :
    ∃ (h : E n → ℂ), ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      ∀ ψ : 𝓢(E n, ℂ), g ψ = ∫ x, ψ x • h x := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hcomp

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_compact.isBounded


  let R' := max R 0
  have hR'_pos : 0 < R' + 1 := by positivity
  have hR'_lt : R' + 1 < R' + 2 := by linarith
  have hR_le_R' : R ≤ R' := le_max_left R 0
  let bump : ContDiffBump (0 : E n) :=
    { rIn := R' + 1
      rOut := R' + 2
      rIn_pos := hR'_pos
      rIn_lt_rOut := hR'_lt }
  let χ₀ : E n → ℝ := bump
  let χ : E n → ℂ := Complex.ofRealCLM ∘ χ₀
  have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hχ_compact : HasCompactSupport χ :=
    bump.hasCompactSupport.comp_left (map_zero _)
  have hχ_tg : Function.HasTemperateGrowth χ :=
    hχ_compact.hasTemperateGrowth hχ_smooth
  have hχ_one : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp only [χ, Function.comp, Complex.ofRealCLM_apply]
    have hx_in : x ∈ Metric.closedBall (0 : E n) bump.rIn := by
      apply Metric.closedBall_subset_closedBall (by linarith : R ≤ R' + 1)
      exact hR hx
    rw [show χ₀ x = (bump : E n → ℝ) x from rfl, bump.one_of_mem_closedBall hx_in]
    simp [Complex.ofReal_one]

  have hχg_eq_g : TemperedDistribution.smulLeftCLM ℂ χ g = g :=
    smulLeftCLM_eq_self_of_one_on_support g K hK_compact hK_supp χ hχ_smooth hχ_compact hχ_one hχ_tg

  obtain ⟨f, hf⟩ := smulLeftCLM_schwartz_of_emptySingSupp g hsing χ hχ_smooth hχ_compact hχ_tg

  have hg_eq : g = schwEmbed f := by rw [← hχg_eq_g, hf]

  refine ⟨⇑f, f.smooth', ?_, ?_⟩
  ·
    have hf_supp : Function.support (⇑f) ⊆ K :=
      schwEmbed_compact_support_of_distrib_compact_support f K hK_compact
        (fun ψ hψ => by rw [← hg_eq]; exact hK_supp ψ hψ)
    exact HasCompactSupport.of_support_subset_isCompact hK_compact hf_supp
  ·
    intro ψ
    rw [hg_eq]
    simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]


/-- A compactly supported distribution with empty singular support is the Schwartz embedding of a
Schwartz function. -/
theorem compactSupport_emptySingSupp_isSchwartz
    (g : 𝓢'(E n, ℂ))
    (hcomp : IsCompactlySupportedDistribution g)
    (hsing : singularSupport g = ∅) :
    ∃ f : 𝓢(E n, ℂ), schwEmbed f = g := by
  obtain ⟨h, hsmooth, hsupp, hrepr⟩ :=
    compactlySupported_emptySingSupp_represented_by_smooth g hcomp hsing
  refine ⟨hsupp.toSchwartzMap hsmooth, ?_⟩
  ext ψ
  simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  exact (hrepr ψ).symm


/-- The conic singular support sphere of any Schwartz function (viewed as a tempered distribution)
is empty. -/
theorem schwartz_conicSingularSupportSphere_empty
    (f : 𝓢(E n, ℂ)) :
    ConicSingularSupportSphere (schwEmbed f) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  rw [ConicSingularSupportSphere, Set.mem_setOf_eq] at hw
  apply hw
  obtain ⟨g, hg⟩ := exists_conicCutoff w
  exact ⟨g, hg, SchwartzMap.smulLeftCLM ℂ g f, smulLeftCLM_schwEmbed_eq g f⟩


end ConeSupport
