/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace LpSpaces

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

/-- The $L^p$ (extended) norm of a function $f : α → E$ with respect to the measure $μ$.
For $1 ≤ p < ∞$, this is $\|f\|_p = \left(\int |f|^p \, dμ\right)^{1/p}$, and for $p = ∞$
it is the essential supremum $\|f\|_∞ = \operatorname{ess\,sup}|f|$. This is a thin wrapper
around `MeasureTheory.eLpNorm`. -/
def eLpNorm (f : α → E) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm f p μ

/-- For a continuous function $f : α → E$ on a compact space $α$ equipped with a Borel measure
of full support, the essential supremum $\|f\|_{L^\infty(μ)}$ coincides with the usual
supremum norm $\|f\|_∞$. This is the continuous-case statement of the essential supremum
property: on $[a,b]$ with $f \in C([a,b])$, $\|f\|_{L^\infty([a,b])} = \|f\|_\infty$. -/
theorem eLpNormEssSup_eq_enorm_continuousMap
    {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {μ : Measure α} [μ.IsOpenPosMeasure]
    {E : Type*} [SeminormedAddCommGroup E] (f : C(α, E)) :
    eLpNormEssSup (fun x => f x) μ = ‖f‖ₑ := by
  simp only [eLpNormEssSup]
  set g : α → ENNReal := fun x => ‖f x‖ₑ
  have hcont : Continuous g := continuous_enorm.comp f.continuous
  have h_essSup_eq : essSup g μ = ⨆ x, g x := by
    apply le_antisymm
    · exact essSup_le_of_ae_le _ (by filter_upwards with x; exact le_iSup g x)
    · apply iSup_le
      intro x
      by_contra h
      simp only [not_le] at h
      have hopen : IsOpen {y | essSup g μ < g y} := hcont.isOpen_preimage _ isOpen_Ioi
      have hpos := hopen.measure_pos μ ⟨x, h⟩
      have hzero : μ {y | essSup g μ < g y} = 0 :=
        measure_mono_null (fun y hy => not_le.mpr hy) (ae_iff.mp (ae_le_essSup (f := g)))
      exact absurd hzero (ne_of_gt hpos)
  rw [h_essSup_eq]
  exact (ContinuousMap.enorm_eq_iSup_enorm f).symm

/-- Essential supremum properties: (1) for any measurable function $f : α → E$ we have
$|f(x)| ≤ \|f\|_{L^\infty(μ)}$ for almost every $x$, and (2) on a compact Hausdorff space
with a Borel measure of full support, the essential supremum of a continuous function
$f : C(α, E)$ equals its usual supremum norm. -/
theorem essSup_properties :
    (∀ {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
      {E : Type*} [ENorm E] (f : α → E),
      ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ MeasureTheory.eLpNormEssSup f μ) ∧
    (∀ {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
      [BorelSpace α] {μ : MeasureTheory.Measure α} [μ.IsOpenPosMeasure]
      {E : Type*} [SeminormedAddCommGroup E] (f : C(α, E)),
      MeasureTheory.eLpNormEssSup (fun x => f x) μ = ‖f‖ₑ) :=
  ⟨fun {_} [_] {_} {_} [_] _ => ae_le_eLpNormEssSup,
   fun {_} [_] [_] [_] [_] {_} [_] {_} [_] f => eLpNormEssSup_eq_enorm_continuousMap f⟩

/-- Integrability part of Hölder's inequality: if $f \in L^p(μ)$ and $g \in L^q(μ)$ with
$\frac{1}{p} + \frac{1}{q} = 1$, then the pointwise product $f \cdot g$ is integrable. -/
theorem holder_integrable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {𝕜 : Type*} [NormedField 𝕜] {p q : ℝ≥0∞}
    {f g : α → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [hpq : ENNReal.HolderConjugate p q] :
    Integrable (f * g) μ :=
  hf.integrable_mul hg

/-- Norm part of Hölder's inequality: if $f \in L^p(μ)$ and $g \in L^q(μ)$ with
$\frac{1}{p} + \frac{1}{q} = 1$, then $\|fg\|_{L^1(μ)} ≤ \|f\|_{L^p(μ)} \cdot \|g\|_{L^q(μ)}$. -/
theorem holder_eLpNorm {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {𝕜 : Type*} [NormedField 𝕜] {p q : ℝ≥0∞}
    {f g : α → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [hpq : ENNReal.HolderConjugate p q] :
    MeasureTheory.eLpNorm (f * g) 1 μ ≤
      MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g q μ := by
  have h := eLpNorm_smul_le_mul_eLpNorm (𝕜 := 𝕜) (E := 𝕜) hg.1 hf.1 (hpqr := hpq)
  simp only [smul_eq_mul] at h
  exact h

/-- Hölder's inequality for $L^p$ spaces: if $1 ≤ p, q ≤ ∞$ with $\frac{1}{p} + \frac{1}{q} = 1$
and $f, g : α → 𝕜$ are measurable with $f \in L^p(μ)$ and $g \in L^q(μ)$, then $fg$ is
integrable and $\int_E |fg| \, dμ ≤ \|f\|_{L^p(μ)} \cdot \|g\|_{L^q(μ)}$. -/
theorem holder_inequality {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {𝕜 : Type*} [NormedField 𝕜] {p q : ℝ≥0∞}
    {f g : α → 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [hpq : ENNReal.HolderConjugate p q] :
    Integrable (f * g) μ ∧
      MeasureTheory.eLpNorm (f * g) 1 μ ≤
        MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g q μ :=
  ⟨holder_integrable hf hg, holder_eLpNorm hf hg⟩

/-- Minkowski's inequality for $L^p$ spaces: for $1 ≤ p ≤ ∞$ and measurable functions
$f, g : α → E$, $\|f + g\|_{L^p(μ)} ≤ \|f\|_{L^p(μ)} + \|g\|_{L^p(μ)}$. This is the
triangle inequality for the $L^p$ norm. -/
theorem minkowski_inequality {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm (f + g) p μ ≤
      MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm g p μ :=
  MeasureTheory.eLpNorm_add_le hf hg hp

/-- Riesz-Fischer theorem: for $1 ≤ p ≤ ∞$ and a complete normed space $E$, the space
$L^p(μ; E)$ is complete, hence a Banach space. -/
theorem riesz_fischer_Lp_completeSpace [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    CompleteSpace (Lp E p μ) :=
  MeasureTheory.Lp.instCompleteSpace

/-- The $L^p$ space $L^p(μ; E) = \{f : α → E : f \text{ measurable and } \|f\|_p < ∞\}$,
quotiented by the equivalence relation of almost-everywhere equality. Implemented as a thin
wrapper around `MeasureTheory.Lp`. -/
def Lp (E : Type*) [NormedAddCommGroup E] (p : ℝ≥0∞)
    {α : Type*} [MeasurableSpace α] (μ : Measure α) : Type _ :=
  ↥(MeasureTheory.Lp E p μ)

/-- For a measurable set $S \subset ℝ$ and a measurable function $g : ℝ → [0, ∞]$, the
integral $\int_S g$ equals the supremum over $n ∈ ℕ$ of the truncated integrals
$\int_{[-n,n] \cap S} g$. This is a monotone convergence statement used to characterize
$L^p$ membership via restricted integrals. -/
theorem lintegral_eq_iSup_lintegral_Icc_inter
    (S : Set ℝ) (hS : MeasurableSet S) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in S, g x ∂volume =
      ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume := by
  rw [← lintegral_indicator hS]
  have h_eq : ∀ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume =
      ∫⁻ x, (Set.Icc (-(n : ℝ)) n ∩ S).indicator g x ∂volume :=
    fun n => (lintegral_indicator (measurableSet_Icc.inter hS) g).symm
  simp_rw [h_eq]
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Set.Icc (-(n : ℝ)) n ∩ S).indicator g with hF_def
  have h_mono : Monotone F := by
    intro m n hmn x
    apply Set.indicator_le_indicator_of_subset
    · exact Set.inter_subset_inter_left S
        (Set.Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn))
    · intro x; exact zero_le _
  have h_sup : (fun x => ⨆ n : ℕ, F n x) = S.indicator g := by
    ext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      apply le_antisymm
      · exact iSup_le (fun n => Set.indicator_le_self _ _ x)
      · obtain ⟨N, hN⟩ := exists_nat_ge |x|
        apply le_iSup_of_le N
        simp only [hF_def]
        rw [Set.indicator_of_mem (show x ∈ Set.Icc (-(N : ℝ)) N ∩ S from
          ⟨⟨neg_le_of_abs_le hN, le_of_abs_le hN⟩, hx⟩)]
    · rw [Set.indicator_of_notMem hx]
      apply le_antisymm
      · apply iSup_le; intro n
        simp only [hF_def]
        rw [Set.indicator_of_notMem (fun h => hx h.2)]
      · exact zero_le _
  have h_meas : ∀ n : ℕ, Measurable (F n) :=
    fun n => hg.indicator (measurableSet_Icc.inter hS)
  rw [← h_sup, lintegral_iSup h_meas h_mono]

/-- Characterization of $L^p$ membership in terms of restricted integrals: for $E \subset ℝ$
measurable and $1 ≤ p < ∞$, a measurable function $f$ belongs to $L^p(E)$ if and only if
$\lim_{n \to \infty} \int_{[-n, n] \cap E} |f|^p < ∞$. -/
theorem memLp_iff_iSup_lintegral_Icc_inter_lt_top
    {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤)
    (S : Set ℝ) (hS : MeasurableSet S) {f : ℝ → F} (hf : Measurable f) :
    MemLp f p (volume.restrict S) ↔
      ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, (‖f x‖ₑ) ^ p.toReal ∂volume < ⊤ := by
  constructor
  · intro hfp
    rw [← lintegral_eq_iSup_lintegral_Icc_inter S hS _ (by measurability)]
    exact (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      hp_ne_zero hp_ne_top).mp hfp.2
  · intro h
    refine ⟨hf.aestronglyMeasurable.restrict, ?_⟩
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    rwa [lintegral_eq_iSup_lintegral_Icc_inter S hS _ (by measurability)]

/-- $L^p(μ; E)$ is a normed additive commutative group for $1 ≤ p ≤ ∞$, with norm
$\|\cdot\|_p$. This is part of the statement that $L^p(E)$ is a normed vector space. -/
instance Lp_instNormedAddCommGroup {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    NormedAddCommGroup (Lp E p μ) :=
  MeasureTheory.Lp.instNormedAddCommGroup

/-- $L^p(μ; E)$ is a normed vector space over $𝕜$ for $1 ≤ p ≤ ∞$. Together with the
additive group instance, this gives the statement that $L^p(E)$ is a normed vector space
under $\|\cdot\|_p$. -/
instance Lp_instNormedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp E p μ) :=
  MeasureTheory.Lp.instNormedSpace



/-- Functions with polynomial decay are in $L^p(ℝ)$ for all $p ≥ 1$: if $f : ℝ → E$ is
measurable and there exist constants $C ≥ 0$ and $q > 1$ such that
$\|f(x)\| ≤ C(1 + |x|)^{-q}$ for almost every $x \in ℝ$, then $f \in L^p(ℝ)$
for every $1 ≤ p ≤ ∞$. -/
theorem memLp_of_polynomial_decay
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_meas : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) {q : ℝ} (hq : 1 < q)
    (hbound : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-q))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp f p volume := by

  by_cases hp_top : p = ⊤
  · subst hp_top
    apply memLp_top_of_bound hf_meas C
    filter_upwards with x
    calc ‖f x‖ ≤ C * (1 + |x|) ^ (-q) := hbound x
      _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_one_of_one_le_of_nonpos
          · linarith [abs_nonneg x]
          · linarith
      _ = C := mul_one C

  · have hp_ne_zero : p ≠ 0 := by positivity
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp_ge_one : (1 : ℝ) ≤ p.toReal := by
      have : (1 : ℝ≥0∞).toReal ≤ p.toReal :=
        (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
      simpa using this

    have hqp : (Module.finrank ℝ ℝ : ℝ) < q * p.toReal := by
      simp [Module.finrank_self]
      calc (1 : ℝ) < q := hq
        _ = q * 1 := (mul_one q).symm
        _ ≤ q * p.toReal := mul_le_mul_of_nonneg_left hp_ge_one (by linarith)

    have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(q * p.toReal))) volume :=
      integrable_one_add_norm hqp
    refine ⟨hf_meas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_top]

    calc ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume
        ≤ ∫⁻ x, ENNReal.ofReal (C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal))) ∂volume := by
          apply lintegral_mono
          intro x
          simp only
          rw [(ofReal_norm_eq_enorm (f x)).symm,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
          apply ENNReal.ofReal_le_ofReal
          have hbound' : ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q) := by
            have := hbound x
            rwa [show |x| = ‖x‖ from (Real.norm_eq_abs x).symm] at this
          calc ‖f x‖ ^ p.toReal
              ≤ (C * (1 + ‖x‖) ^ (-q)) ^ p.toReal :=
                Real.rpow_le_rpow (norm_nonneg _) hbound' hp_pos.le
            _ = C ^ p.toReal * ((1 + ‖x‖) ^ (-q)) ^ p.toReal :=
                Real.mul_rpow hC (Real.rpow_nonneg (by positivity) _)
            _ = C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal)) := by
                congr 1
                rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖x‖)]
                ring_nf
      _ < ⊤ := by
          simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
          rw [lintegral_const_mul _ (by measurability)]
          apply ENNReal.mul_lt_top
          · exact ENNReal.ofReal_lt_top
          · rw [← lintegral_enorm_of_nonneg (fun x => Real.rpow_nonneg (by positivity) _)]
            exact hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral

end LpSpaces
