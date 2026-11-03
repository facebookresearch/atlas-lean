/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Atlas.DifferentialAnalysis.code.DistributionSupport
import Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity

open scoped SchwartzMap
open TemperedDistribution MvPolynomial

noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

/-- The **principal symbol** of a polynomial `P` of (assumed) order `m`:
the degree-`m` homogeneous component of `P`. -/
def principalSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent m P

/-- Unfolding lemma: `principalSymbol n m P = homogeneousComponent m P`. -/
@[simp]
theorem principalSymbol_def (m : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    principalSymbol n m P = homogeneousComponent m P :=
  rfl

/-- A polynomial `P(ξ)` (of order `m`) is **elliptic** if its principal
symbol `P_m(ξ)` does not vanish for any nonzero real vector `ξ ∈ ℝⁿ`.
(See Melrose, Definition 11.11.) -/
def IsElliptic (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P) ≠ 0

/-- The **Fourier symbol** `P(2πiξ)` of the differential operator `P(D)`,
viewed as a function `ℝⁿ → ℂ`. -/
def polySymbol (P : MvPolynomial (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) P

/-- The **constant-coefficient differential operator** `P(D)` acting on
tempered distributions, defined as the Fourier multiplier with symbol
`P(2πiξ)`. -/
def constCoeffDiffOp (P : MvPolynomial (Fin n) ℂ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ (polySymbol n P)

/-- A tempered distribution `E` is a **fundamental solution** of `P(D)`
if `P(D) E = δ₀`. -/
def IsTemperedFundamentalSolution (P : MvPolynomial (Fin n) ℂ)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  constCoeffDiffOp n P E = TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))



open Set Function MeasureTheory

section SingularSupport

variable {n : ℕ}

/-- A tempered distribution `u` is **smooth near** a point `x₀` if there
exists an open neighbourhood `U` of `x₀` on which `u` is represented by a
smooth function (under pairing with Schwartz functions supported in `U`). -/
def isSmoothNear (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧
    ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        u φ = ∫ y, φ y • f y

/-- The **singular support** of `u`: the set of points `x₀` near which
`u` fails to be smooth. -/
def singularSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x₀ | ¬ isSmoothNear u x₀}

/-- `u` **vanishes on** the set `U` if it sends every test function
supported in `U` to zero. -/
def vanishesOn (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) → u φ = 0

end SingularSupport

section OperatorProperties

variable {n : ℕ}




/-- **Partition of `u`** by a temperate cutoff: for any `χ` of temperate
growth, `χ · u + (1 - χ) · u = u`. -/
theorem smulLeftCLM_add_complement
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : Function.HasTemperateGrowth χ) :
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

/-- If `χ` is a smooth temperate cutoff supported in an open set `U` on
which `u` is represented by a smooth function `f`, then `χ · u` is
globally smooth — represented by `χ · f`. -/
theorem smulLeft_globally_smooth_of_supported_in_smooth_region
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : ∀ x, x ∉ U → χ x = 0)
    (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
      u φ = ∫ y, φ y • f y)
    (hχ_temp : Function.HasTemperateGrowth χ) :
    ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear (smulLeftCLM ℂ χ u) y := by
  intro y


  refine ⟨Set.univ, isOpen_univ, Set.mem_univ y, χ * f, hχ_smooth.mul hf_smooth,
    fun φ _ => ?_⟩
  simp only [smulLeftCLM_apply_apply]


  have hχφ_supp : ∀ z, z ∉ U → (SchwartzMap.smulLeftCLM ℂ χ φ) z = 0 := by
    intro z hz
    simp only [SchwartzMap.smulLeftCLM]
    split
    · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
        ContinuousLinearMap.flip_apply]
      rw [hχ_supp z hz, zero_smul]
    · simp
  rw [hf_eq (SchwartzMap.smulLeftCLM ℂ χ φ) hχφ_supp]
  congr 1; ext z
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.flip_apply, Pi.mul_apply]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  · exact absurd hχ_temp ‹_›

/-- If `χ ≡ 1` on the open set `V`, then `(1 - χ) · u` **vanishes** on
`V`. -/
theorem smulLeft_complement_vanishesOn
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (V : Set (EuclideanSpace ℝ (Fin n)))
    (hχ_one : ∀ x ∈ V, χ x = 1)
    (h1χ_temp : Function.HasTemperateGrowth (1 - χ)) :
    vanishesOn (smulLeftCLM ℂ (1 - χ) u) V := by
  intro φ hφ_supp
  simp only [smulLeftCLM_apply_apply]

  suffices h : SchwartzMap.smulLeftCLM ℂ (1 - χ) φ = 0 by rw [h, map_zero]
  ext x
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.flip_apply, SchwartzMap.zero_apply]
    by_cases hxV : x ∈ V
    · rw [show (1 - χ) x = 1 - χ x from rfl, hχ_one x hxV, sub_self, zero_smul]
    · rw [hφ_supp x hxV, smul_zero]
  · simp





/-- The sum of a globally smooth distribution `v` and one (`w`) that
vanishes on a neighbourhood `U` of `x₀` is smooth near `x₀`. -/
theorem smooth_plus_vanishing_is_smooth
    (v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hx : x₀ ∈ U)
    (hv : ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear v y)
    (hw : vanishesOn w U) :
    isSmoothNear (v + w) x₀ := by

  obtain ⟨V, hV_open, hx_V, f, hf_smooth, hv_eq⟩ := hv x₀

  refine ⟨V ∩ U, hV_open.inter hU, ⟨hx_V, hx⟩, f, hf_smooth, ?_⟩
  intro φ hφ_supp

  simp only [UniformConvergenceCLM.add_apply]

  have hφ_V : ∀ y, y ∉ V → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨hyV, _⟩ => hy hyV)
  have hφ_U : ∀ y, y ∉ U → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨_, hyU⟩ => hy hyU)

  rw [hv_eq φ hφ_V]

  rw [hw φ hφ_U, add_zero]

/-- If `u` vanishes on the open set `U`, then `u` is **smooth** at every
point of `U` (with smooth representative `0`). -/
theorem isSmoothNear_of_vanishesOn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hv : vanishesOn u U)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ U) :
    isSmoothNear u x₀ :=
  ⟨U, hU, hx₀, 0, contDiff_const, fun φ hφ => by rw [hv φ hφ]; simp⟩




end OperatorProperties

section SingularSupportInclusion

variable {n : ℕ}


end SingularSupportInclusion

section WeakConvergence

open Filter Topology

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scalar multiplication is sequentially weakly continuous in `𝓢'`:
if `u j → u₀`, then `c · u j → c · u₀`. -/
theorem tendsto_const_smul {p : Filter ι} {u : ι → 𝓢'(E, F)} {u₀ : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (c : ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) :=
  ((continuous_const_smul c).tendsto _).comp hu

/-- Addition is sequentially weakly continuous in `𝓢'`:
if `u j → u₀` and `u' j → u₀'`, then `u j + u' j → u₀ + u₀'`. -/
theorem tendsto_add {p : Filter ι} {u u' : ι → 𝓢'(E, F)} {u₀ u₀' : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀')) :
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) :=
  hu.add hu'

/-- `P(D)` is sequentially weakly continuous: weakly convergent sequences
of distributions are taken to weakly convergent sequences. -/
theorem tendsto_constCoeffDiffOp {n : ℕ} {p : Filter ι}
    {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (P : MvPolynomial (Fin n) ℂ) :
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p
      (𝓝 (constCoeffDiffOp n P u₀)) :=
  ((constCoeffDiffOp n P).continuous.tendsto _).comp hu

/-- Left multiplication by a function `g` (as a CLM on `𝓢'`) is
sequentially weakly continuous. -/
theorem tendsto_smul_left {p : Filter ι} {u : ι → 𝓢'(E, F)} {u₀ : 𝓢'(E, F)}
    (hu : Tendsto u p (𝓝 u₀)) (g : E → ℂ) :
    Tendsto (fun j => TemperedDistribution.smulLeftCLM F g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM F g u₀)) :=
  ((TemperedDistribution.smulLeftCLM F g).continuous.tendsto _).comp hu

/-- **Combined weak continuity package.** Packaging the four preceding
weak-continuity results into one statement; this is the conjunction
recorded as `proposition_11_2` (Melrose, Proposition 11.2). -/
theorem tendsto_smul_add_diffOp_smulLeft {n : ℕ} {p : Filter ι}
    {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hu : Tendsto u p (𝓝 u₀)) (hu' : Tendsto u' p (𝓝 u₀'))
    (c : ℂ) (P : MvPolynomial (Fin n) ℂ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) ∧
    Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) ∧
    Tendsto (fun j => constCoeffDiffOp n P (u j)) p
      (𝓝 (constCoeffDiffOp n P u₀)) ∧
    Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p
      (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
  ⟨tendsto_const_smul hu c, tendsto_add hu hu',
   tendsto_constCoeffDiffOp hu P, tendsto_smul_left hu g⟩

alias proposition_11_2 := tendsto_smul_add_diffOp_smulLeft

end WeakConvergence

section HypoellipticRegularity
open scoped Pointwise

variable {n}

/-- A tempered distribution `F` is a **parametrix** for `P(D)` if
`P(D) F - δ₀` has empty singular support, i.e. it is smooth everywhere.
(See Melrose, Definition 11.8.) -/
def IsParametrix (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  singularSupport
    (constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) = ∅

/-- `P(D)` is **hypoelliptic** if it admits a parametrix `F` whose
singular support is contained in `{0}`. -/
def IsHypoelliptic (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
    IsParametrix P F ∧
    singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))}


/-- **Existence of a smooth compactly-supported cutoff equal to `1` near
the origin.** Used to localise parametrices near `0`. -/
theorem smooth_cutoff_near_zero_for_parametrix (n : ℕ) :
    ∃ (φ : EuclideanSpace ℝ (Fin n) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧
      HasCompactSupport φ ∧
      Function.HasTemperateGrowth φ ∧
      (∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∈ U ∧ ∀ x ∈ U, φ x = 1) := by

  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨1, 2, one_pos, one_lt_two⟩

  refine ⟨fun x => (b x : ℂ), ?_, ?_, ?_, ?_⟩
  ·
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  ·
    exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  ·
    exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  ·
    refine ⟨Metric.ball 0 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_⟩
    intro x hx
    show (b x : ℂ) = 1
    have : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [this]


/-- If `φ` is a smooth compactly-supported temperate function, then
`φ · F` has compact distributional support contained in `tsupport φ`. -/
theorem smulLeft_compactSupp_gives_compact_support
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → ψ y = 0) → (TemperedDistribution.smulLeftCLM ℂ φ F) ψ = 0 := by
  refine ⟨tsupport φ, hφ_supp, fun ψ hψ => ?_⟩
  simp only [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ φ ψ = 0 by rw [h, map_zero]
  ext y
  simp only [SchwartzMap.smulLeftCLM_apply_apply hφ_temp, SchwartzMap.zero_apply]
  by_cases hy : y ∈ tsupport φ
  · rw [hψ y hy, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]


/-- **Singular support contracts under left multiplication:**
`singsupp(φ · F) ⊆ singsupp F` for `φ` a smooth temperate function. -/
theorem singularSupport_smulLeft_subset_of_temperate
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport (TemperedDistribution.smulLeftCLM ℂ φ F) ⊆ singularSupport F := by
  intro x₀ hx₀
  simp only [singularSupport, Set.mem_setOf_eq] at hx₀ ⊢
  intro hF_smooth
  apply hx₀
  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hF_smooth
  refine ⟨U, hU_open, hx₀_U, fun y => φ y * f y, hφ_smooth.mul hf_smooth, fun ψ hψ => ?_⟩
  rw [smulLeftCLM_apply_apply]
  have hφψ_supp : ∀ y, y ∉ U → (SchwartzMap.smulLeftCLM ℂ φ ψ) y = 0 := by
    intro y hy
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
    rw [hψ y hy, smul_zero]
  rw [hf_eq _ hφψ_supp]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
  simp only [smul_eq_mul]
  ring










/-- **Smooth-remainder splitting.** For any `u`, the parametrix identity
gives a decomposition `u = v + w` with `v = P(D) F - δ₀ ∗ … = ψ` globally
smooth (when `F` has compact d-support and is a parametrix). -/
theorem parametrix_smooth_remainder_exists
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      v + w = u ∧
      (∀ y, isSmoothNear v y) := by

  set ψ := constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hψ_smooth : ∀ y, isSmoothNear ψ y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y
  exact ⟨ψ, u - ψ, by abel, hψ_smooth⟩













end HypoellipticRegularity

section EllipticHypoelliptic

variable {n}




/-- Auxiliary: any `Cᵏ` function that agrees with `F` away from a small
ball around `0` exists — in fact `F` itself is `Cᵏ` and the conclusion is
trivial in this formulation. -/
theorem temperateGrowth_inverseFT_contDiff_away
    {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) → ℂ)
    (hQ : Function.HasTemperateGrowth Q)
    (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF_tg : Function.HasTemperateGrowth F)
    (hF_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∫ ξ, Q ξ • (FourierTransformInv.fourierInv φ : EuclideanSpace ℝ (Fin n) → ℂ) ξ =
          ∫ y, φ y • F y)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧
      ∀ y, ε / 2 < ‖y‖ → g y = F y :=


  ⟨F, hF_tg.1.of_le (by exact_mod_cast le_top), fun _ _ => rfl⟩















/-- **Smoothness of the Fourier symbol.** The map
`ξ ↦ P(2πiξ) : ℝⁿ → ℂ` is `C^∞`. -/
theorem polySymbol_contDiff (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (polySymbol n P) := by
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
        2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.contDiff _)
      exact contDiff_const.mul hx
    exact hP.mul hcoord


/-- **Smoothness of the parametrix symbol at zeros of `P̂`.** At a point
`ξ₀` where the Fourier symbol of `P` vanishes (and where the cutoff `φ`
equals `1` on a neighbourhood), the regularised symbol
`(1 - φ(ξ)) · P̂(ξ)⁻¹` is smooth — locally it is identically zero. -/
theorem contDiffAt_parametrix_symbol_at_zero
    {n : ℕ} {m : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : IsElliptic n m P) (hn : 0 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ ≠ 0 ∨ φ ξ = 1)
    (hφ_nhd_zero : ∀ ξ : EuclideanSpace ℝ (Fin n),
      polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1)
    (ξ₀ : EuclideanSpace ℝ (Fin n))
    (h_zero : polySymbol n P ξ₀ = 0)
    (h_phi : φ ξ₀ = 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) ξ₀ := by

  have heq : (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) =ᶠ[nhds ξ₀] (fun _ => (0 : ℂ)) := by
    filter_upwards [hφ_nhd_zero ξ₀ h_zero] with ξ hξ
    simp [hξ]
  exact contDiffAt_const.congr_of_eventuallyEq heq







/-- **Temperate growth of the Fourier symbol.** The polynomial symbol
`ξ ↦ P(2πiξ)` has temperate growth. -/
theorem polySymbol_hasTemperateGrowth
    (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    Function.HasTemperateGrowth (polySymbol n P) := by
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
        2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hc : Function.HasTemperateGrowth (fun _ : EuclideanSpace ℝ (Fin n) =>
        (2 * ↑Real.pi * Complex.I : ℂ)) := Function.HasTemperateGrowth.const _
      have hx : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.hasTemperateGrowth.comp (EuclideanSpace.proj j).hasTemperateGrowth
      exact hc.mul hx
    exact hP.mul hcoord

set_option maxHeartbeats 400000 in
/-- **Compactly-supported multipliers give globally smooth distributions.**
If the Fourier multiplier `φ` is smooth and compactly supported, then
`φ(D) δ₀ = ℱ^{-1} φ` is a Schwartz function, hence smooth near every
point. -/
theorem compactSupport_fourierMultiplier_delta_isSmoothNear
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_temp : Function.HasTemperateGrowth φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear
      (TemperedDistribution.fourierMultiplierCLM ℂ φ
        (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀ := by
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  let φ_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := hφ_compact.toSchwartzMap hφ_smooth
  let f_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := FourierTransformInv.fourierInv φ_sch
  refine ⟨f_sch, f_sch.smooth', fun ψ _ => ?_⟩
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply, TemperedDistribution.delta_apply]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have heq : ∀ v, (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv ψ)) v =
      φ v • (FourierTransformInv.fourierInv ψ) v :=
    fun v => SchwartzMap.smulLeftCLM_apply_apply hφ_temp _ v
  simp_rw [heq]
  simp_rw [show ∀ y, ψ y • (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y =
      (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y • ψ y from fun y => mul_comm _ _]
  exact (SchwartzMap.integral_fourierInv_smul_eq φ_sch ψ).symm



/-- **`Q(D) δ₀` is a parametrix.** Given symbol data `(Q, φ)` with
`Q · P̂ = 1 - φ` and `φ(D) δ₀` smooth everywhere, the difference
`P(D) (Q(D) δ₀) - δ₀` equals `-φ(D) δ₀` and is therefore smooth near every
point. In particular `Q(D) δ₀` is a parametrix for `P(D)`. -/
theorem elliptic_parametrix_isParametrix_proof
    {n : ℕ} {m : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : IsElliptic n m P)
    {Q φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hQ : Function.HasTemperateGrowth Q)
    (hφ : Function.HasTemperateGrowth φ)
    (hPt : Function.HasTemperateGrowth (polySymbol n P))
    (hQP : ∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ)
    (hφs : ∀ x₀, isSmoothNear
      (TemperedDistribution.fourierMultiplierCLM ℂ φ
        (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear
      (constCoeffDiffOp n P
        (TemperedDistribution.fourierMultiplierCLM ℂ Q
          (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) -
       TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) x₀ := by

  set δ₀ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))


  have hcomp : constCoeffDiffOp n P
      (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) =
      TemperedDistribution.fourierMultiplierCLM ℂ (Q * polySymbol n P) δ₀ := by
    simp only [constCoeffDiffOp]
    exact TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hQ hPt δ₀
  have hQP_eq : Q * polySymbol n P = 1 - φ := by
    ext ξ; exact hQP ξ
  have hkey : constCoeffDiffOp n P
      (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) - δ₀ =
      -(TemperedDistribution.fourierMultiplierCLM ℂ φ δ₀) := by
    rw [hcomp, hQP_eq]

    have h1φ : Function.HasTemperateGrowth (1 - φ) :=
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub hφ
    ext u
    simp only [TemperedDistribution.fourierMultiplierCLM_apply_apply,
      UniformConvergenceCLM.sub_apply, UniformConvergenceCLM.neg_apply]
    have hsum : SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u) +
        SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u) =
        FourierTransformInv.fourierInv u := by
      ext x
      simp only [SchwartzMap.add_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply h1φ, SchwartzMap.smulLeftCLM_apply_apply hφ]
      simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul, sub_add_cancel]
    have hab : FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u)) +
        FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u)) = u := by
      rw [← FourierAdd.fourier_add, hsum, FourierTransform.fourier_fourierInv_eq]
    have hlin : δ₀ (FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u))) +
        δ₀ (FourierTransform.fourier
        (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u))) = δ₀ u := by
      rw [← map_add δ₀, hab]
    linear_combination hlin

  rw [hkey]

  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hφs x₀
  exact ⟨U, hU_open, hx₀_U, -f, hf_smooth.neg, fun ψ hψ => by
    simp only [UniformConvergenceCLM.neg_apply, hf_eq ψ hψ, Pi.neg_apply, smul_neg,
      integral_neg]⟩







end EllipticHypoelliptic

section PoissonEquation

open Filter Topology

variable {n}

/-- A **smooth function vanishing at infinity** (with all derivatives):
a smooth complex-valued function on `ℝⁿ` whose iterated derivatives of
every order tend to zero on the cocompact filter. Used as the target class
for Liouville-type uniqueness results for the Laplacian. -/
structure SmoothZeroAtInfty (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  iteratedFDeriv_zero_at_infty' (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

namespace SmoothZeroAtInfty

variable {n : ℕ}

/-- `SmoothZeroAtInfty` is coercible to a function via its underlying
`toFun` field, with the obvious injectivity. -/
instance instFunLike : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe u := u.toFun
  coe_injective' u v h := by cases u; cases v; congr

/-- Pointwise equality of `SmoothZeroAtInfty` functions implies equality. -/
@[ext]
theorem ext {u v : SmoothZeroAtInfty n} (h : ∀ x, u x = v x) : u = v :=
  DFunLike.ext u v h

/-- Smoothness of the underlying function of a `SmoothZeroAtInfty`. -/
theorem smooth (u : SmoothZeroAtInfty n) : ContDiff ℝ (⊤ : ℕ∞) u :=
  u.smooth'

/-- For every order `m`, the norm of the `m`-th iterated derivative of a
`SmoothZeroAtInfty` function tends to zero on the cocompact filter. -/
theorem iteratedFDeriv_zero_at_infty (u : SmoothZeroAtInfty n) (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m u x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
  u.iteratedFDeriv_zero_at_infty' m

end SmoothZeroAtInfty

/-- The **Laplacian polynomial** `P(X) = Σⱼ Xⱼ²`, whose associated
constant-coefficient differential operator is the Laplacian
`Δ = Σⱼ ∂ⱼ²` (up to the usual `(2πi)²` factor coming from the Fourier
normalisation). -/
def laplacianPoly : MvPolynomial (Fin n) ℂ :=
  ∑ j : Fin n, MvPolynomial.X j ^ 2

/-- The **Laplacian** as a continuous linear operator on tempered
distributions, defined via the constant-coefficient differential operator
machinery applied to `laplacianPoly`. -/
def laplacianOp :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  constCoeffDiffOp n (laplacianPoly)

end PoissonEquation

end DifferentialOperators

namespace DifferentialOperators

/-- **Smoothness of polynomial evaluation.** Evaluating a real multivariate
polynomial on the coordinates of `ℝⁿ` yields a `C^∞` function. -/
lemma contDiff_mvPolynomial_eval {n₀ : ℕ} (Q : MvPolynomial (Fin n₀) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n₀) =>
      MvPolynomial.eval (fun i => ξ i) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_piLp_apply 2)

/-- **Closed-form norm of derivatives of `1/x`.** On an open subset of
`ℝ`, the norm of the `k`-th iterated Fréchet derivative of `x ↦ x⁻¹`
equals `k! · ‖y‖^{-(k+1)}`. -/
lemma norm_iteratedFDerivWithin_inv_eq (k : ℕ) (y : ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hys : y ∈ s) :
    ‖iteratedFDerivWithin ℝ k Inv.inv s y‖ = ↑(k.factorial) * ‖y‖⁻¹ ^ (k + 1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hfun : Inv.inv = fun z : ℝ => 1 / z := by ext z; exact (one_div z).symm
  rw [hfun, iteratedDerivWithin_one_div k hs hys]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  rw [show (-1 : ℤ) - ↑k = -(↑(k + 1) : ℤ) by omega]
  rw [zpow_neg, norm_inv, zpow_natCast, norm_pow, one_div, inv_pow]


/-- **Smoothness of `1/P(ξ)` at non-vanishing points.** Wherever the
polynomial `P` does not vanish, the function `ξ ↦ 1/P(ξ)` is `C^∞`. -/
lemma contDiffAt_inv_mvPolynomial_eval {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ :=
  (contDiff_mvPolynomial_eval P).contDiffAt.inv hP

/-- **Explicit derivative of `1/P(ξ)`.** At any non-vanishing point, the
Fréchet derivative of `ξ ↦ 1/P(ξ)` equals `-P(ξ)⁻² · dP(ξ)`. -/
lemma hasFDerivAt_inv_mvPolynomial_eval {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    HasFDerivAt (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹)
      (-(MvPolynomial.eval (fun i => ξ i) P)⁻¹ ^ 2 •
        fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
          MvPolynomial.eval (fun i => ξ' i) P) ξ)
      ξ := by
  have hP_diff : HasFDerivAt
      (fun ξ' : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ' i) P)
      (fderiv ℝ (fun ξ' => MvPolynomial.eval (fun i => ξ' i) P) ξ) ξ :=
    ((contDiff_mvPolynomial_eval P).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hasFDerivAt_inv hP).comp ξ hP_diff
  convert h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm, sq, inv_mul_eq_div]

/-- **Norm bound for the derivative of `1/P(ξ)`.** Combining the explicit
formula with the multiplicativity of norms,
`‖d(1/P)(ξ)‖ ≤ ‖dP(ξ)‖ / ‖P(ξ)‖²`. -/
lemma norm_fderiv_inv_mvPolynomial_eval_le {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ)
    (ξ : EuclideanSpace ℝ (Fin n₀))
    (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
    ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ ≤
      ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
        MvPolynomial.eval (fun i => ξ' i) P) ξ‖ /
        ‖MvPolynomial.eval (fun i => ξ i) P‖ ^ 2 := by
  rw [(hasFDerivAt_inv_mvPolynomial_eval P ξ hP).fderiv]
  rw [norm_smul, norm_neg, norm_pow, norm_inv, inv_pow, div_eq_mul_inv, mul_comm]

/-- **Recursive identity for higher derivatives of `1/P`.** The norm of the
`(k+1)`-th iterated derivative of `1/P` equals the norm of the `k`-th
iterated derivative of its first derivative. -/
lemma norm_iteratedFDeriv_succ_eq_norm_iteratedFDeriv_fderiv_inv_poly
    {n₀ : ℕ} (P : MvPolynomial (Fin n₀) ℝ) (k : ℕ)
    (ξ : EuclideanSpace ℝ (Fin n₀)) :
    ‖iteratedFDeriv ℝ (k + 1) (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ =
    ‖iteratedFDeriv ℝ k (fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) =>
      (MvPolynomial.eval (fun i => ξ' i) P)⁻¹)) ξ‖ :=
  norm_iteratedFDeriv_fderiv.symm

end DifferentialOperators


namespace DifferentialOperators

open MeasureTheory

/-- **Non-degeneracy of the Laplacian polynomial.** For `n ≥ 1`,
`Σⱼ Xⱼ²` is nonzero in `ℂ[X₀, …, X_{n-1}]`. -/
lemma laplacianPoly_ne_zero {n : ℕ} (hn : 1 ≤ n) : laplacianPoly (n := n) ≠ 0 := by
  unfold laplacianPoly
  intro h
  have h0 : Fin n := ⟨0, by omega⟩
  let e₀ : Fin n → ℂ := fun j => if j = h0 then 1 else 0
  have heval := congr_arg (MvPolynomial.eval e₀) h
  simp only [map_sum, map_zero, MvPolynomial.eval_pow, MvPolynomial.eval_X] at heval
  have key : (e₀ h0) ^ 2 = 1 := by simp [e₀]
  have hterm : ∑ j : Fin n, (e₀ j) ^ 2 = 1 := by
    have hzero : ∀ j : Fin n, j ≠ h0 → (e₀ j) ^ 2 = 0 := by
      intro j hj; simp [e₀, hj]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ h0)]
    rw [key]
    have : ∑ j ∈ Finset.univ.erase h0, (e₀ j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hzero j (Finset.ne_of_mem_erase hj)
    rw [this]; ring
  exact one_ne_zero (hterm.symm.trans heval)


open Filter Topology

/-- The **classical Laplacian relation** between smooth functions
`f, g : ℝⁿ → ℂ`: `g(x) = -Σⱼ ∂_j² f(x)` for every `x`. (The convention sign
comes from the Fourier multiplier `-|2πξ|²` of `Δ`.) -/
def IsLaplacianOf_DO (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))













end DifferentialOperators

open SchwartzMap MeasureTheory Distribution

open scoped Topology

namespace Distribution

section SingularSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [BorelSpace E]

/-- A tempered distribution `u` is **smooth on** the set `s` if there
is a globally smooth `g : E → ℂ` such that `u φ = ∫ φ g` for every
Schwartz function `φ` with `tsupport φ ⊆ s`. -/
def IsSmoothOn (u : 𝓢'(E, ℂ)) (s : Set E) : Prop :=
  ∃ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
    ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ s → u φ = ∫ x, φ x • g x

/-- The **singular support** of `u`: complement of the union of all open
sets on which `u` is represented by a smooth function. -/
def singularSupport (u : 𝓢'(E, ℂ)) : Set E :=
  (⋃₀ {s | IsSmoothOn u s ∧ IsOpen s})ᶜ

end SingularSupport

end Distribution
end

noncomputable section

open scoped SchwartzMap Topology
open Distribution SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace DifferentialOperators

/-- A tempered distribution `v` has **compact distributional support** if
its `dsupport` is a compact subset of the underlying space. -/
def HasCompactDsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(E, F)) : Prop :=
  IsCompact (dsupport v)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- **Continuity of translation** on Schwartz space. The map
`x ↦ ψ(· - x)` from `E` to `𝓢(E, ℂ)` is continuous. -/
theorem schwartz_compSubConstCLM_continuous
    (ψ : 𝓢(E, ℂ)) :
    Continuous (fun x : E => compSubConstCLM ℂ x ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, (schwartz_withSeminorms ℂ E ℂ).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  set C := 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ
  set Kx := (1 + ‖x₀‖) ^ k * 2 ^ k
  set K := Kx * C
  set δ := min 1 (ε / (K + 1))
  have hδ_pos : 0 < δ := by positivity
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun {x} hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hx1 : ‖x - x₀‖ ≤ 1 := le_trans (le_of_lt hx) (min_le_left _ _)
  show (schwartzSeminormFamily ℂ E ℂ (k, n)) _ < ε
  rw [SchwartzMap.compSubConstCLM_sub_eq ψ x x₀]
  set φ := SchwartzMap.compSubConstCLM ℂ (x - x₀) ψ - ψ
  have hbound := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ k n φ x₀
  have hsup_bound : ((Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) φ ≤
      C * ‖x - x₀‖ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro ⟨j, m⟩ hjm
    rw [Finset.mem_Iic] at hjm
    have hj : j ≤ k := hjm.1
    have hm : m ≤ n := hjm.2
    have hsub := SchwartzMap.seminorm_translate_sub_le ψ j m (x - x₀) hx1
    have h2pow : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
    have hfin_mono : (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) ≤
        (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) := by
      apply Finset.sup_mono
      intro ⟨a, b⟩ hab
      simp only [Finset.mem_Iic] at hab ⊢
      exact ⟨le_trans hab.1 hj, le_trans hab.2 (Nat.succ_le_succ hm)⟩
    calc (SchwartzMap.seminorm ℂ j m) φ
        ≤ 2 ^ j * (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
            ‖x - x₀‖ := hsub
      _ ≤ 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
            ‖x - x₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul h2pow (hfin_mono ψ) (by positivity) (by positivity)
      _ = C * ‖x - x₀‖ := by ring
  calc (schwartzSeminormFamily ℂ E ℂ (k, n)) (SchwartzMap.compSubConstCLM ℂ x₀ φ)
      ≤ Kx * (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ := hbound
    _ ≤ Kx * (C * ‖x - x₀‖) := mul_le_mul_of_nonneg_left hsup_bound (by positivity)
    _ < ε := by
        have hK_nonneg : 0 ≤ K := by positivity
        have hK1 : 0 < K + 1 := by positivity
        calc Kx * (C * ‖x - x₀‖)
            ≤ Kx * (C * δ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (le_of_lt hx) (by positivity)
          _ = K * δ := by ring
          _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK_nonneg
          _ < ε := by
              have : K / (K + 1) < 1 := by rw [div_lt_one hK1]; linarith
              calc K * (ε / (K + 1)) = (K / (K + 1)) * ε := by ring
                _ < 1 * ε := mul_lt_mul_of_pos_right this hε
                _ = ε := one_mul ε

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The `n`-th iterated derivative of `z ↦ fderiv f z h` factors through
the application map `T ↦ T h`. -/
theorem iteratedFDeriv_fderiv_apply_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f) (h : E) (y : E) :
    iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y =
      (ContinuousLinearMap.apply ℝ F h).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ f) y) := by
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  exact (ContinuousLinearMap.apply ℝ F h).iteratedFDeriv_comp_left hfderiv le_rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Norm bound: `‖∂ⁿ (z ↦ Df(z)·h)‖ ≤ ‖∂ⁿ⁺¹ f‖ · ‖h‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f) (h : E) (y : E) :
    ‖iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖h‖ := by
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  have hle := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f) (c := h) (x := y)
    hfderiv (le_refl _)
  rw [norm_iteratedFDeriv_fderiv] at hle
  linarith [mul_comm ‖h‖ ‖iteratedFDeriv ℝ (n + 1) f y‖]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Taylor remainder estimate.** For a `C²` map `g`, the first-order
Taylor remainder is `O(‖h‖²)` with constant given by a bound on the second
derivative. -/
theorem norm_iteratedFDeriv_taylor_remainder_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : ContDiff ℝ 2 g) (C : ℝ)
    (hC : ∀ z : E, ‖iteratedFDeriv ℝ 2 g z‖ ≤ C)
    (y h : E) :
    ‖g (y - h) - g y + (fderiv ℝ g y) h‖ ≤ C * ‖h‖ ^ 2 := by

  set Φ : E → F := fun z => g z - g y - (fderiv ℝ g y) (z - y) with hΦ_def
  have hΦy : Φ y = 0 := by simp [hΦ_def, sub_self]
  have hΦyh : Φ (y - h) = g (y - h) - g y + (fderiv ℝ g y) h := by
    simp only [hΦ_def, map_sub]; abel
  have hne2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hg_diff : Differentiable ℝ g := hg.differentiable hne2

  have hΦ_hasFDeriv : ∀ z, HasFDerivAt Φ (fderiv ℝ g z - fderiv ℝ g y) z := by
    intro z
    have hg_has : HasFDerivAt g (fderiv ℝ g z) z := (hg_diff z).hasFDerivAt
    have h1 : HasFDerivAt (fun w => g w - g y) (fderiv ℝ g z) z := by
      have h := hg_has.sub (hasFDerivAt_const (g y) z); rwa [sub_zero] at h
    have h2 : HasFDerivAt (fun w => (fderiv ℝ g y) (w - y)) (fderiv ℝ g y) z := by
      have hsub : HasFDerivAt (fun w => w - y) (ContinuousLinearMap.id ℝ E) z := by
        have h := (hasFDerivAt_id (𝕜 := ℝ) z).sub (hasFDerivAt_const y z); rwa [sub_zero] at h
      have h := (fderiv ℝ g y).hasFDerivAt.comp z hsub; rwa [ContinuousLinearMap.comp_id] at h
    convert h1.sub h2 using 1

  have hfderiv_g_diff : Differentiable ℝ (fderiv ℝ g) := by
    have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := by
      have : ContDiff ℝ (↑(1 : ℕ) + 1 : WithTop ℕ∞) g := by exact_mod_cast hg
      exact (contDiff_succ_iff_fderiv.mp this).2.2
    exact hg1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

  have hfderiv_fderiv_bound : ∀ w : E, ‖fderiv ℝ (fderiv ℝ g) w‖ ≤ C := by
    intro w
    have heq : ‖fderiv ℝ (fderiv ℝ g) w‖ = ‖iteratedFDeriv ℝ 2 g w‖ := by
      conv_rhs => rw [show (2 : ℕ) = 1 + 1 from rfl]
      rw [← norm_iteratedFDeriv_fderiv (n := 1),
        ← norm_iteratedFDeriv_fderiv (n := 0) (f := fderiv ℝ g)]
      simp
    linarith [hC w]

  have hinner_mvt : ∀ z : E, ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := by
    intro z
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (fun x _ => hfderiv_g_diff x) (fun x _ => hfderiv_fderiv_bound x)
      convex_univ (Set.mem_univ z) (Set.mem_univ y)
    rw [norm_sub_rev, norm_sub_rev y z] at hmvt
    exact hmvt
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC y)

  have hbound_on_seg :
      ∀ z ∈ segment ℝ y (y - h), ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖h‖ := by
    intro z hz
    have hzy : ‖z - y‖ ≤ ‖h‖ := by
      rw [segment_eq_image' ℝ y (y - h)] at hz
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
      simp only [sub_sub_cancel_left]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1
    calc ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := hinner_mvt z
      _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_left hzy hC_nonneg

  have houter := (convex_segment y (y - h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ g z - fderiv ℝ g y)
    (fun z hz => (hΦ_hasFDeriv z).hasFDerivWithinAt)
    hbound_on_seg
    (left_mem_segment ℝ y (y - h))
    (right_mem_segment ℝ y (y - h))
  rw [hΦyh, hΦy, sub_zero] at houter
  calc ‖g (y - h) - g y + (fderiv ℝ g y) h‖
      ≤ C * ‖h‖ * ‖y - h - y‖ := houter
    _ = C * ‖h‖ * ‖h‖ := by rw [sub_sub_cancel_left, norm_neg]
    _ = C * ‖h‖ ^ 2 := by ring










omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Multiplying a Schwartz function by a smooth compactly-supported real
cutoff `χ` produces another Schwartz function `χ · f`. -/
noncomputable def cutoffMul (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (hχcs.smul_right (f' := ⇑f)).toSchwartzMap
    ((hχcd.of_le le_top).smul f.smooth')

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Evaluation lemma for the cutoff product:
`(cutoffMul χ … f) y = χ y • f y`. -/
@[simp]
theorem cutoffMul_apply_eq (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) (y : E) :
    (cutoffMul χ hχcs hχcd f) y = χ y • f y := by
  unfold cutoffMul
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  exact Complex.real_smul

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Function-level identity for the cutoff product:
`⇑(cutoffMul χ … f) = fun y => χ y • f y`. -/
theorem cutoffMul_coe_eq (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) :
    ⇑(cutoffMul χ hχcs hχcd f) = fun y => χ y • f y :=
  funext (cutoffMul_apply_eq χ hχcs hχcd f)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Zero-weight Schwartz seminorms are translation-invariant.** Since
`(0, m)`-seminorms involve no polynomial weight, the translated function
`φ(· - x)` has the same `(0, m)`-seminorm as `φ`. -/
theorem seminorm_compSubConst_zero_weight (x : E) (φ : 𝓢(E, ℂ)) (m : ℕ) :
    SchwartzMap.seminorm ℂ 0 m (compSubConstCLM ℂ x φ) = SchwartzMap.seminorm ℂ 0 m φ := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    rw [hc, iteratedFDeriv_comp_sub]
    have h := le_seminorm ℂ 0 m φ (y - x)
    simp only [pow_zero, one_mul] at h; exact h
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    have h := le_seminorm ℂ 0 m (compSubConstCLM ℂ x φ) (y + x)
    simp only [pow_zero, one_mul] at h
    rw [hc, iteratedFDeriv_comp_sub, add_sub_cancel_right] at h
    exact h

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
set_option maxHeartbeats 6400000 in
/-- **Cutoff–translation seminorm bound.** Bounded uniformly in the
translation parameter `x`, the `(k, n)`-Schwartz seminorm of the cutoff of
`φ(· - x)` is controlled by a fixed finite supremum of seminorms of `φ`. -/
theorem cutoff_translation_seminorm_bound
    (χ : E → ℝ) (hχcs : HasCompactSupport χ) (hχcd : ContDiff ℝ ⊤ χ) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢(E, ℂ)) (x : E),
      SchwartzMap.seminorm ℂ k n (cutoffMul χ hχcs hχcd (compSubConstCLM ℂ x φ)) ≤
        C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
  let s : Finset (ℕ × ℕ) := (Finset.range (n + 1)).image (fun j => (0, j))

  have hRk : ∃ Rk : ℝ, 0 ≤ Rk ∧ ∀ y ∈ tsupport χ, ‖y‖ ^ k ≤ Rk := by
    by_cases hne : (tsupport χ).Nonempty
    · obtain ⟨y₀, _, hmax⟩ := hχcs.isCompact.exists_isMaxOn hne
        (continuous_norm.pow k).continuousOn
      exact ⟨‖y₀‖ ^ k, by positivity, fun y hy => hmax hy⟩
    · exact ⟨0, le_refl 0, fun y hy =>
        ((Set.not_nonempty_iff_eq_empty.mp hne) ▸ hy).elim⟩
  obtain ⟨Rk, hRk_nn, hRk_bd⟩ := hRk

  have hBi : ∀ i ∈ Finset.range (n + 1),
      ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ y : E,
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi := by
    intro i _
    have hcsi : HasCompactSupport (iteratedFDeriv ℝ i χ) := hχcs.iteratedFDeriv i
    have hci : Continuous (iteratedFDeriv ℝ i χ) :=
      (hχcd.of_le le_top).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    by_cases hne : (tsupport (iteratedFDeriv ℝ i χ)).Nonempty
    · obtain ⟨z₀, _, hmax⟩ := hcsi.isCompact.exists_isMaxOn hne
        (continuous_norm.comp hci).continuousOn
      refine ⟨(n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ z₀‖, by positivity, fun y => ?_⟩
      gcongr
      by_cases hy : y ∈ tsupport (iteratedFDeriv ℝ i χ)
      · exact hmax hy
      · have : iteratedFDeriv ℝ i χ y = 0 := by
          have : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
            fun h => hy (subset_tsupport _ h)
          rwa [Function.mem_support, not_not] at this
        simp [this]
    · exact ⟨0, le_refl 0, fun y => by
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have : iteratedFDeriv ℝ i χ y = 0 := by
          have : y ∉ Function.support (iteratedFDeriv ℝ i χ) := by
            intro h; exact (hne ▸ subset_tsupport _ h).elim
          rwa [Function.mem_support, not_not] at this
        simp [this]⟩


  have hBi_exists : ∀ i ∈ Finset.range (n + 1), ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : E, (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ B := hBi

  let Bi' : ℕ → ℝ := fun i =>
    if h : i ∈ Finset.range (n + 1) then (hBi_exists i h).choose else 0
  have hBi'_nn : ∀ i, 0 ≤ Bi' i := by
    intro i; simp only [Bi']; split_ifs with h
    · exact (hBi_exists i h).choose_spec.1
    · exact le_refl 0
  have hBi'_bd : ∀ i ∈ Finset.range (n + 1), ∀ y : E,
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := by
    intro i hi y; simp only [Bi', dif_pos hi]
    exact (hBi_exists i hi).choose_spec.2 y
  let Ctotal : ℝ := Rk * ∑ i ∈ Finset.range (n + 1), Bi' i
  refine ⟨s, Ctotal, ?_, fun φ x => ?_⟩
  · apply mul_nonneg hRk_nn
    exact Finset.sum_nonneg fun i _ => hBi'_nn i
  apply SchwartzMap.seminorm_le_bound ℂ k n
  · exact mul_nonneg (mul_nonneg hRk_nn
      (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)
  intro y
  rw [cutoffMul_coe_eq]
  set ψ := compSubConstCLM ℂ x φ
  have hχ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) χ := hχcd.of_le le_top
  have hψ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) ψ := by
    apply ψ.smooth'.of_le; exact_mod_cast le_top
  have hsmul_le := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hχ_cd hψ_cd y le_rfl
  by_cases hy_supp : y ∈ tsupport χ
  ·
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1),
            ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖) *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            Rk * Bi' i * SchwartzMap.seminorm ℂ 0 (n - i) φ := by
          apply Finset.sum_le_sum; intro i hi
          have h1 : ‖y‖ ^ k ≤ Rk := hRk_bd y hy_supp
          have h2 : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := hBi'_bd i hi y
          have h3 : ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ ≤ SchwartzMap.seminorm ℂ 0 (n - i) φ :=
            calc ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖
                ≤ SchwartzMap.seminorm ℂ 0 (n - i) ψ :=
                  SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ (n - i) y
              _ = SchwartzMap.seminorm ℂ 0 (n - i) φ :=
                  seminorm_compSubConst_zero_weight x φ (n - i)
          exact mul_le_mul (mul_le_mul h1 h2 (by positivity) hRk_nn)
            h3 (norm_nonneg _) (mul_nonneg hRk_nn (hBi'_nn i))
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            Rk * Bi' i * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          apply Finset.sum_le_sum; intro i hi
          apply mul_le_mul_of_nonneg_left
          · have hmem : (0, n - i) ∈ s :=
              Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), rfl⟩
            rw [← SchwartzMap.schwartzSeminormFamily_apply ℂ E ℂ 0 (n - i)]
            exact (Finset.le_sup hmem : schwartzSeminormFamily ℂ E ℂ (0, n - i) ≤ _) φ
          · exact mul_nonneg hRk_nn (hBi'_nn i)
      _ = Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          simp only [Ctotal, Finset.mul_sum]; rw [Finset.sum_mul]
  ·
    have hχ_zero : ∀ i : ℕ, iteratedFDeriv ℝ i χ y = 0 := by
      intro i
      have h1 : y ∉ tsupport (iteratedFDeriv ℝ i χ) :=
        fun h => hy_supp (tsupport_iteratedFDeriv_subset i h)
      have h2 : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
        fun h => h1 (subset_tsupport _ h)
      rwa [Function.mem_support, not_not] at h2
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
            ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
          exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ‖y‖ ^ k * 0 := by
          congr 1; apply Finset.sum_eq_zero; intro i _; simp [hχ_zero i]
      _ ≤ Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
          simp only [mul_zero]
          exact mul_nonneg (mul_nonneg hRk_nn
            (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)




/-- Elementary numeric inequality used in `one_add_pow_bound`:
`a + a^N ≤ 1 + a^(N+1)` for `a ≥ 0`. -/
lemma add_pow_nonneg_le_one_add (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    a + a ^ N ≤ 1 + a ^ (N + 1) := by
  suffices h : 0 ≤ (a - 1) * (a ^ N - 1) by nlinarith [pow_succ a N]
  by_cases h : a ≤ 1
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [pow_le_one₀ ha h (n := N)])
  · push Not at h
    exact mul_nonneg (by linarith) (by linarith [one_le_pow₀ h.le (n := N)])


/-- **Polynomial growth lemma.** `(1 + a)^N ≤ 2^N · (1 + a^N)` for
`a ≥ 0`, used to control polynomial weights in Schwartz seminorms. -/
lemma one_add_pow_bound (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc (1 + a) ^ (N + 1) = (1 + a) ^ N * (1 + a) := pow_succ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) * (1 + a) := by gcongr
      _ = 2 ^ N * (1 + a + a ^ N + a ^ N * a) := by ring
      _ = 2 ^ N * (1 + a + a ^ N + a ^ (N + 1)) := by rw [pow_succ]
      _ ≤ 2 ^ N * (2 * (1 + a ^ (N + 1))) := by
          gcongr; linarith [add_pow_nonneg_le_one_add a ha N]
      _ = 2 ^ (N + 1) * (1 + a ^ (N + 1)) := by ring










section PolynomialGrowthBound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Coordinate bound.** Each coordinate of a Euclidean vector is bounded
in absolute value by its norm: `|ξ i| ≤ ‖ξ‖`. -/
lemma EuclideanSpace.abs_coord_le_norm {m : ℕ} (ξ : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    |ξ i| ≤ ‖ξ‖ := by
  have h1 : (ξ i) ^ 2 ≤ ∑ j : Fin m, (ξ j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (ξ j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ‖ξ‖ ^ 2 = ∑ j : Fin m, (ξ j) ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
  have h3 : (ξ i) ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith
  exact abs_le_of_sq_le_sq h3 (norm_nonneg ξ)

/-- **Polynomial growth bound.** The evaluation of a multivariate
polynomial `Q` of total degree `d` at points of `ℝⁿ` is bounded by a
constant times `(1 + ‖ξ‖)^d`. -/
theorem mvPolynomial_eval_bound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, C > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖MvPolynomial.eval (fun i => ξ i) Q‖ ≤ C * (1 + ‖ξ‖) ^ Q.totalDegree := by
  refine ⟨max 1 (∑ d ∈ Q.support, |Q.coeff d|), by positivity, fun ξ => ?_⟩
  set f : Fin n → ℝ := fun i => ξ i
  have heval : MvPolynomial.eval f Q = ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i :=
    MvPolynomial.eval_eq' f Q
  rw [heval]
  have h1le : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have hnle : ‖ξ‖ ≤ 1 + ‖ξ‖ := le_add_of_nonneg_left (by norm_num)
  have hmono : ∀ d ∈ Q.support,
      ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ ≤
        |Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree := by
    intro d hd
    rw [Real.norm_eq_abs, abs_mul]
    have hprod_bound : |∏ i : Fin n, f i ^ d i| ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
      rw [Finset.abs_prod]
      have step1 : ∀ i : Fin n, |f i ^ d i| ≤ ‖ξ‖ ^ d i := by
        intro i; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (EuclideanSpace.abs_coord_le_norm ξ i) _
      have step2 : ∏ i : Fin n, |f i ^ d i| ≤ ∏ i : Fin n, ‖ξ‖ ^ d i :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => step1 i)
      have step3 : ∏ i : Fin n, ‖ξ‖ ^ d i = ‖ξ‖ ^ ∑ i : Fin n, d i :=
        Finset.prod_pow_eq_pow_sum _ _ _
      have step4 : ∑ i : Fin n, d i ≤ Q.totalDegree := by
        have h := MvPolynomial.le_totalDegree hd
        rw [Finsupp.sum_fintype] at h
        · exact h
        · intros; rfl
      calc ∏ i : Fin n, |f i ^ d i|
          ≤ ‖ξ‖ ^ ∑ i : Fin n, d i := step3 ▸ step2
        _ ≤ (1 + ‖ξ‖) ^ ∑ i : Fin n, d i :=
            pow_le_pow_left₀ (norm_nonneg _) hnle _
        _ ≤ (1 + ‖ξ‖) ^ Q.totalDegree :=
            pow_le_pow_right₀ h1le step4
    exact mul_le_mul_of_nonneg_left hprod_bound (abs_nonneg _)
  calc ‖∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i‖
      ≤ ∑ d ∈ Q.support, ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Q.support, (|Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree) :=
        Finset.sum_le_sum hmono
    _ = (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ max 1 (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _)
        positivity

end PolynomialGrowthBound

section ParametrixSymbol

open Function MvPolynomial

/-- A **smooth function with compact support** automatically belongs to
the Schwartz class; this packages the conversion. -/
theorem compactSupport_contDiff_to_schwartz
    {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ ξ, (ψ : EuclideanSpace ℝ (Fin n) → ℂ) ξ = φ ξ :=
  ⟨hφ_supp.toSchwartzMap hφ_smooth,
   fun ξ => hφ_supp.toSchwartzMap_toFun hφ_smooth ξ⟩






end ParametrixSymbol

end DifferentialOperators
