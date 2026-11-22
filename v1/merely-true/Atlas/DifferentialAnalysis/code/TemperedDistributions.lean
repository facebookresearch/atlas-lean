/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support

noncomputable section

open scoped SchwartzMap ENNReal NNReal LineDeriv
open SchwartzMap MeasureTheory ContinuousLinearMap

namespace TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A linear functional on Schwartz space is continuous as soon as its norm seminorm is
dominated by a finite sup of Schwartz seminorms times a constant. -/
theorem continuous_of_seminorm_bound
    (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)
    (hbound : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0),
      (normSeminorm ℂ ℂ).comp u ≤ C • s.sup (schwartzSeminormFamily ℂ E ℂ)) :
    Continuous u :=
  (schwartz_withSeminorms ℂ E ℂ).continuous_normedSpace_rng ℂ u hbound

/-- Conversely, every continuous linear functional on Schwartz space is dominated by a finite
sup of Schwartz seminorms times a constant. -/
theorem seminorm_bound_of_continuous
    (u : 𝓢(E, ℂ) →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0),
      (normSeminorm ℂ ℂ).comp u.toLinearMap ≤
        C • s.sup (schwartzSeminormFamily ℂ E ℂ) := by
  have hcont : Continuous ((normSeminorm ℂ ℂ).comp u.toLinearMap) := by
    show Continuous (fun x => ‖u x‖)
    exact continuous_norm.comp u.continuous
  obtain ⟨s, C, _, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) _ hcont
  exact ⟨s, C, hle⟩

/-- Continuity of a linear functional on Schwartz space is equivalent to a Schwartz-seminorm
bound (Melrose Prop 7.3): this is the characterisation of tempered distributions. -/
theorem continuous_iff_seminorm_bound
    (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) :
    Continuous u ↔
      ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0),
        (normSeminorm ℂ ℂ).comp u ≤ C • s.sup (schwartzSeminormFamily ℂ E ℂ) := by
  constructor
  · intro hcont
    exact seminorm_bound_of_continuous ⟨u, hcont⟩
  · exact continuous_of_seminorm_bound u

/-- Continuous embedding `Lp(F, μ) → 𝓢'(E, F)` sending an `Lᵖ`-function to the tempered
distribution it represents. -/
def lpToTemperedDistributionCLM
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
    (μ : Measure E) [μ.HasTemperateGrowth]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp F p μ →L[ℂ] 𝓢'(E, F) :=
  Lp.toTemperedDistributionCLM F μ p

/-- Distributional directional derivative in direction `m`: a continuous linear endomorphism
of `𝓢'(E, F)` given by `u ↦ u ∘ (-∂_m)`. -/
def distribDerivCLM (m : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  LineDeriv.lineDerivOpCLM ℂ (𝓢'(E, F)) m

/-- The definitional unfolding of `distribDerivCLM`: it pairs `u` with `-(∂_m φ)`. -/
@[simp]
theorem distribDerivCLM_apply (m : E) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    distribDerivCLM m u φ = u (-(∂_{m} φ)) :=
  TemperedDistribution.lineDerivOp_apply_apply u φ m

/-- Distributional multiplication by a (necessarily temperate) function `g : E → ℂ`, as a
continuous linear endomorphism of `𝓢'(E, F)`. -/
def distribMulCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  TemperedDistribution.smulLeftCLM F g

/-- The definitional unfolding of `distribMulCLM g`: it pairs `u` with `g · φ`. -/
@[simp]
theorem distribMulCLM_apply (g : E → ℂ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    distribMulCLM g u φ = u (SchwartzMap.smulLeftCLM ℂ g φ) :=
  TemperedDistribution.smulLeftCLM_apply_apply g u φ

section Lemma71

open scoped ContDiff

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Equivalence of two formulations of Schwartz decay for a smooth function: the standard
`‖x‖ᵏ` polynomial growth control matches the variant using `(1 + ‖x‖)ᵏ`. -/
theorem schwartz_iff_oneAddNorm_decay {f : E → G} (hsmooth : ContDiff ℝ ∞ f) :
    (∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) ↔
    (∀ k n : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) := by
  constructor
  · intro hdecay k n
    let g : 𝓢(E, G) := ⟨f, hsmooth, hdecay⟩
    use 2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    intro x
    have := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl g x
    simpa using this
  · intro hdecay k n
    obtain ⟨C, hC⟩ := hdecay k n
    exact ⟨C, fun x => le_trans (by gcongr; linarith [norm_nonneg x]) (hC x)⟩

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

/-- Differentiating in `𝓢(ℝ, G)` shifts a Schwartz seminorm: the `(k, n)`-seminorm of `f'` is
bounded by the `(k, n + 1)`-seminorm of `f`. -/
theorem SchwartzMap.seminorm_derivCLM_le (k n : ℕ) (f : 𝓢(ℝ, G)) :
    SchwartzMap.seminorm 𝕜 k n (SchwartzMap.derivCLM 𝕜 G f) ≤
      SchwartzMap.seminorm 𝕜 k (n + 1) f := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity)
  intro x
  have h : (SchwartzMap.derivCLM 𝕜 G f : ℝ → G) = deriv f := by ext; rfl
  rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ',
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact SchwartzMap.le_seminorm 𝕜 k (n + 1) f x

omit [SMulCommClass ℝ 𝕜 G] in
/-- The `m`-th power of `derivCLM` equals its `m`-fold function iterate. -/
theorem SchwartzMap.derivCLM_pow_eq_iterate (m : ℕ) (f : 𝓢(ℝ, G)) :
    ((SchwartzMap.derivCLM 𝕜 G) ^ m) f =
    ((SchwartzMap.derivCLM 𝕜 G) : 𝓢(ℝ, G) → 𝓢(ℝ, G))^[m] f := by
  induction m generalizing f with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, Function.iterate_succ, Function.comp, ih]

/-- Polynomial monomials `x ↦ xᵅ` are of temperate growth. -/
theorem monomial_hasTemperateGrowth (α : ℕ) :
    (fun (x : ℝ) => x ^ α).HasTemperateGrowth := by fun_prop

/-- Continuous linear operator on `𝓢(ℝ, G)` given by `f ↦ x^α · f^(β)`, i.e. the multiplication
by the monomial `xᵅ` composed with `β`-fold differentiation. -/
def SchwartzMap.polyMulDerivCLM (α β : ℕ) :
    𝓢(ℝ, G) →L[ℝ] 𝓢(ℝ, G) :=
  SchwartzMap.smulLeftCLM G (fun x : ℝ => x ^ α) ∘L (SchwartzMap.derivCLM ℝ G) ^ β

end Lemma71

section Lemma74

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

/-- Every continuous linear endomorphism of `𝓢(E, G)` is bounded with respect to the Schwartz
seminorm family in the sense that each seminorm of `T(f)` is dominated by a finite sum of
seminorms of `f`. -/
theorem seminorm_bound_of_continuous_linearMap
    (T : 𝓢(E, G) →L[𝕜] 𝓢(E, G)) :
    Seminorm.IsBounded (schwartzSeminormFamily 𝕜 E G)
      (schwartzSeminormFamily 𝕜 E G) T.toLinearMap := by
  intro m
  have hcont : Continuous ((schwartzSeminormFamily 𝕜 E G m).comp T.toLinearMap) := by
    exact (schwartz_withSeminorms 𝕜 E G).continuous_seminorm m |>.comp T.continuous
  obtain ⟨s, C, _, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms 𝕜 E G) _ hcont
  exact ⟨s, C, hle⟩

/-- Conversely, a linear endomorphism of `𝓢(E, G)` that is bounded with respect to the
Schwartz seminorm family is automatically continuous. -/
theorem continuous_of_seminorm_bound_linearMap
    (T : 𝓢(E, G) →ₗ[𝕜] 𝓢(E, G))
    (hbound : Seminorm.IsBounded (schwartzSeminormFamily 𝕜 E G)
      (schwartzSeminormFamily 𝕜 E G) T) :
    Continuous T :=
  WithSeminorms.continuous_of_isBounded
    (schwartz_withSeminorms 𝕜 E G) (schwartz_withSeminorms 𝕜 E G) T hbound

end Lemma74

section DsupportSchwartz

open scoped ContDiff
open Distribution TemperedDistribution MeasureTheory.Measure Filter Topology

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [(volume : Measure E).IsAddHaarMeasure]
  [CompleteSpace F]

omit [CompleteSpace F] in
/-- The distributional support of the tempered distribution attached to a Schwartz function `ψ`
is contained in the closure of the support of `ψ`. -/
theorem dsupport_schwartz_subset_tsupport (ψ : 𝓢(E, F)) :
    Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) ⊆ tsupport (⇑ψ) := by
  rw [← Set.compl_subset_compl]
  intro p hp
  rw [Set.mem_compl_iff] at hp
  rw [Set.mem_compl_iff, Distribution.notMem_dsupport_iff]
  refine ⟨(tsupport (⇑ψ))ᶜ, ?_, isOpen_compl_iff.mpr (isClosed_tsupport _), ?_⟩
  · intro φ hφ
    simp only [toTemperedDistributionCLM_apply_apply]
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport (⇑φ)
      · simp [image_eq_zero_of_notMem_tsupport (hφ hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  · exact Set.mem_compl hp

/-- The support of a Schwartz function `ψ` is contained in the distributional support of the
attached tempered distribution. -/
theorem support_subset_dsupport_schwartz (ψ : 𝓢(E, F)) :
    Function.support (⇑ψ) ⊆
      Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) := by
  rw [← Set.compl_subset_compl]
  intro p hp
  rw [Set.mem_compl_iff, Distribution.notMem_dsupport_iff] at hp
  obtain ⟨U, hU_van, hU_open, hp_mem⟩ := hp
  rw [Set.mem_compl_iff, Function.mem_support, not_not]
  have h_test : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ U → ∫ x, g x • ψ x = 0 := by
    intro g hg_diff hg_cpt hg_tsup
    have hg_cpt' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_cpt.comp_left rfl
    have hg_diff' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) :=
      Complex.ofRealCLM.contDiff.comp hg_diff
    set φ := hg_cpt'.toSchwartzMap hg_diff'
    have hφ_tsup : tsupport (⇑φ) ⊆ U := by
      show tsupport (Complex.ofRealCLM ∘ g) ⊆ U
      exact (tsupport_comp_subset rfl _).trans hg_tsup
    have h_apply := hU_van φ hφ_tsup
    simp only [toTemperedDistributionCLM_apply_apply] at h_apply
    have h_integral_eq : (∫ x, g x • ψ x) = ∫ x, φ x • ψ x := by
      apply integral_congr_ae
      filter_upwards with x
      change g x • ψ x = (Complex.ofRealCLM ∘ g) x • ψ x
      rw [Function.comp_apply, Complex.ofRealCLM_apply, Complex.coe_smul]
    rw [h_integral_eq]
    exact h_apply
  have hψ_loc_int : LocallyIntegrableOn (⇑ψ) U :=
    ψ.continuous.continuousOn.locallyIntegrableOn hU_open.measurableSet
  have h_ae_zero := hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hψ_loc_int h_test
  have h_ae_restrict : (⇑ψ) =ᵐ[volume.restrict U] (0 : E → F) := by
    rw [EventuallyEq, ae_restrict_iff' hU_open.measurableSet]
    filter_upwards [h_ae_zero] with x hx hxU
    exact hx hxU
  have h_eqOn : Set.EqOn (⇑ψ) 0 U :=
    eqOn_open_of_ae_eq h_ae_restrict hU_open
      ψ.continuous.continuousOn continuous_const.continuousOn
  exact h_eqOn hp_mem

/-- The distributional support of (the tempered distribution attached to) a Schwartz function
coincides with its topological support. -/
theorem dsupport_schwartz_eq_tsupport (ψ : 𝓢(E, F)) :
    Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) = tsupport (⇑ψ) := by
  apply Set.Subset.antisymm
  · exact dsupport_schwartz_subset_tsupport ψ
  · exact Distribution.isClosed_dsupport.closure_subset_iff.mpr
      (support_subset_dsupport_schwartz ψ)

/-- Joint statement: the distributional support of any tempered distribution is closed, and on
Schwartz functions the distributional support coincides with the topological support. -/
theorem dsupport_closed_and_eq_tsupport (u : 𝓢'(E, F)) (ψ : 𝓢(E, F)) :
    IsClosed (Distribution.dsupport u) ∧
      Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) = tsupport (⇑ψ) :=
  ⟨Distribution.isClosed_dsupport, dsupport_schwartz_eq_tsupport ψ⟩

end DsupportSchwartz

end TemperedDistributions

end
