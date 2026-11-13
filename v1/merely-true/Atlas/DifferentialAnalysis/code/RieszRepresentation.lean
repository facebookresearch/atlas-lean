/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence

import Mathlib.Topology.UrysohnsLemma
import Atlas.DifferentialAnalysis.code.JordanDecomposition
import Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

noncomputable section

open MeasureTheory Set TopologicalSpace CompactlySupported
  CompactlySupportedContinuousMap
open scoped ZeroAtInfty ENNReal BoundedContinuousFunction

namespace RieszRepresentation

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

section PositiveCase

end PositiveCase

omit [MeasurableSpace X] [BorelSpace X] in
/-- Any continuous function vanishing at infinity can be uniformly approximated to within `ε`
by a continuous function of compact support, via a Urysohn-type cutoff. -/
lemma c0_approx_by_cc (f : C₀(X, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C_c(X, ℝ), ‖f - (g : C₀(X, ℝ))‖ ≤ ε := by
  have hf := f.zero_at_infty'
  rw [Metric.tendsto_nhds] at hf
  have hev := hf ε hε
  rw [Filter.hasBasis_cocompact.eventually_iff] at hev
  obtain ⟨K, hK, hKf⟩ := hev
  obtain ⟨χ, hχ1, _, hχsupp, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  let gfun : C(X, ℝ) := χ * f.toContinuousMap
  have gsupp : HasCompactSupport gfun := HasCompactSupport.mul_right hχsupp
  let g : C_c(X, ℝ) := ⟨gfun, gsupp⟩
  use g
  rw [show ‖f - (g : C₀(X, ℝ))‖ = ‖(f - (g : C₀(X, ℝ))).toBCF‖ from rfl]
  rw [BoundedContinuousFunction.norm_le (le_of_lt hε)]
  intro x
  simp only [Real.norm_eq_abs]
  have hval : (f - (g : C₀(X, ℝ))).toBCF x = f x - χ x * f x := rfl
  rw [hval]
  by_cases hx : x ∈ K
  · have : χ x = 1 := by simpa using hχ1 hx
    rw [this, one_mul, sub_self, abs_zero]; exact le_of_lt hε
  · have hfx : |f x| < ε := by
      have := hKf hx; simp only [Real.dist_0_eq_abs] at this
      exact (show |f x| = |f.toFun x| from rfl) ▸ this
    have : |f x - χ x * f x| = |f x| * |1 - χ x| := by
      rw [show f x - χ x * f x = f x * (1 - χ x) from by ring]; exact abs_mul _ _
    rw [this]
    calc |f x| * |1 - χ x|
      _ ≤ |f x| * 1 := by
          gcongr; rw [abs_le]
          exact ⟨by linarith [(hχ01 x).2], by linarith [(hχ01 x).1]⟩
      _ = |f x| := mul_one _
      _ ≤ ε := le_of_lt hfx

end RieszRepresentation

end

open MeasureTheory Measure Filter BoundedContinuousFunction
open scoped ZeroAtInfty CompactlySupported ENNReal BoundedContinuousFunction

noncomputable section

/-- Uniqueness in Riesz representation: two Jordan decompositions of the same continuous linear
functional on `C₀(X, ℝ)` give the same signed measure (on every measurable set). -/
lemma riesz_uniqueness
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μP μN νP νN : Measure X)
    [IsFiniteMeasure μP] [IsFiniteMeasure μN]
    [IsFiniteMeasure νP] [IsFiniteMeasure νN]
    [μP.Regular] [μN.Regular] [νP.Regular] [νN.Regular]
    (h : ∀ f : ZeroAtInftyContinuousMap X ℝ,
      ∫ x, f x ∂μP - ∫ x, f x ∂μN = ∫ x, f x ∂νP - ∫ x, f x ∂νN)
    (E : Set X) (_hE : MeasurableSet E) :
    μP.real E - μN.real E = νP.real E - νN.real E := by
  have hCc : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μP - ∫ x, f x ∂μN =
      ∫ x, f x ∂νP - ∫ x, f x ∂νN := fun f => h (f : C₀(X, ℝ))
  have hsum : ∀ f : C_c(X, ℝ), ∫ x, f x ∂(μP + νN) = ∫ x, f x ∂(μN + νP) := by
    intro f
    rw [integral_add_measure (f.integrable) (f.integrable),
        integral_add_measure (f.integrable) (f.integrable)]
    linarith [hCc f]
  haveI : IsFiniteMeasure (μP + νN) := isFiniteMeasureAdd
  haveI : IsFiniteMeasure (μN + νP) := isFiniteMeasureAdd
  haveI : μP.InnerRegular := inferInstance
  haveI : νN.InnerRegular := inferInstance
  haveI : μN.InnerRegular := inferInstance
  haveI : νP.InnerRegular := inferInstance
  haveI : (μP + νN).Regular := inferInstance
  haveI : (μN + νP).Regular := inferInstance
  have heq : μP + νN = μN + νP :=
    Measure.ext_of_integral_eq_on_compactlySupported hsum
  have h1 : (μP + νN) E = (μN + νP) E := congr_arg (· E) heq
  simp only [Measure.coe_add, Pi.add_apply] at h1
  rw [Measure.real, Measure.real, Measure.real, Measure.real]
  have := congr_arg ENNReal.toReal h1
  rw [ENNReal.toReal_add (measure_ne_top μP E) (measure_ne_top νN E),
      ENNReal.toReal_add (measure_ne_top μN E) (measure_ne_top νP E)] at this
  linarith

/-- Restrict a positive continuous linear functional on `C₀(X, ℝ)` to the subspace of compactly
supported continuous functions, producing a positive linear functional on `C_c(X, ℝ)`. -/
def restrictPositiveCLFToCc
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (u : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ)
    (hu : ContinuousFunctions.IsPositiveFunctional u) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  MeasuresAndSigmaAlgebras.restrictC0ToCc u.toLinearMap (fun f hf => hu f hf)

/-- The Riesz measure obtained from a positive continuous linear functional on `C₀(X, ℝ)` is
finite, with total mass bounded by `‖u‖`. -/
lemma rieszMeasure_finite_of_positive_CLF
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (u : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ)
    (hu : ContinuousFunctions.IsPositiveFunctional u) :
    IsFiniteMeasure (RealRMK.rieszMeasure (restrictPositiveCLFToCc u hu)) := by
  set Λ := restrictPositiveCLFToCc u hu
  set μ := RealRMK.rieszMeasure Λ
  haveI := RealRMK.regular_rieszMeasure Λ
  constructor


  suffices hbnd : ∀ K : Set X, IsCompact K → μ K ≤ ENNReal.ofReal ‖u‖ by
    by_contra h
    push Not at h
    have htop : μ Set.univ = ⊤ := top_le_iff.mp h
    have hreg := (RealRMK.regular_rieszMeasure Λ).innerRegular
    have : ENNReal.ofReal ‖u‖ + 1 < μ Set.univ := by
      rw [htop]; exact le_top.lt_of_ne (by simp)
    obtain ⟨K, _, hKcompact, hKmeas⟩ := hreg isOpen_univ _ this
    have : μ K ≤ ENNReal.ofReal ‖u‖ := hbnd K hKcompact
    have : ENNReal.ofReal ‖u‖ + 1 ≤ μ K := le_of_lt hKmeas
    have : ENNReal.ofReal ‖u‖ + 1 ≤ ENNReal.ofReal ‖u‖ := le_trans ‹_› ‹_ ≤ ENNReal.ofReal ‖u‖›
    exact absurd this (not_le.mpr (ENNReal.lt_add_right (by simp) one_ne_zero))
  intro K hK

  obtain ⟨χ, hχ1, _, hχsupp, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  let g : C_c(X, ℝ) := ⟨χ, hχsupp⟩
  calc μ K
    _ ≤ ENNReal.ofReal (Λ g) :=
        RealRMK.rieszMeasure_le_of_eq_one Λ (fun x => (hχ01 x).1) hK (fun x hx => hχ1 hx)
    _ ≤ ENNReal.ofReal ‖u‖ := by
        apply ENNReal.ofReal_le_ofReal


        show u (MeasuresAndSigmaAlgebras.inclusionCcC0 g) ≤ ‖u‖
        calc u (MeasuresAndSigmaAlgebras.inclusionCcC0 g)
          _ ≤ |u (MeasuresAndSigmaAlgebras.inclusionCcC0 g)| := le_abs_self _
          _ = ‖u (MeasuresAndSigmaAlgebras.inclusionCcC0 g)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖u‖ * ‖MeasuresAndSigmaAlgebras.inclusionCcC0 g‖ := u.le_opNorm _
          _ ≤ ‖u‖ * 1 := by
              gcongr
              rw [show ‖MeasuresAndSigmaAlgebras.inclusionCcC0 g‖ =
                ‖(MeasuresAndSigmaAlgebras.inclusionCcC0 g).toBCF‖ from rfl]
              rw [BoundedContinuousFunction.norm_le (by positivity)]
              intro x
              simp only [Real.norm_eq_abs]
              rw [abs_le]
              have hgx : (MeasuresAndSigmaAlgebras.inclusionCcC0 g).toBCF x = χ x := rfl
              constructor
              · rw [hgx]; linarith [(hχ01 x).1]
              · rw [hgx]; exact_mod_cast (hχ01 x).2
          _ = ‖u‖ := mul_one _

/-- A continuous linear functional on `C₀(X, ℝ)` that agrees with integration against a finite
measure on every compactly supported continuous function in fact agrees with it on all of
`C₀(X, ℝ)`. -/
lemma clf_eq_integral_of_agree_on_cc
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (v : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ)
    (μ : Measure X) [IsFiniteMeasure μ]
    (hcc : ∀ g : C_c(X, ℝ), v (g : C₀(X, ℝ)) = ∫ x, g x ∂μ)
    (f : C₀(X, ℝ)) :
    v f = ∫ x, f x ∂μ := by
  by_contra hne
  have _hne' : 0 < |v f - ∫ x, f x ∂μ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C := ‖v‖ + (μ Set.univ).toReal + 1
  have hC : 0 < C := by positivity
  set δ := |v f - ∫ x, f x ∂μ| / (2 * C)
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hg⟩ := RieszRepresentation.c0_approx_by_cc f δ hδ
  have hcg : v (g : C₀(X, ℝ)) = ∫ x, (g : C₀(X, ℝ)) x ∂μ := hcc g
  have hv_bound : |v f - v (g : C₀(X, ℝ))| ≤ ‖v‖ * δ := by
    rw [show v f - v (g : C₀(X, ℝ)) = v (f - (g : C₀(X, ℝ))) from by rw [map_sub]]
    calc |v (f - (g : C₀(X, ℝ)))|
      _ = ‖v (f - (g : C₀(X, ℝ)))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v‖ * ‖f - (g : C₀(X, ℝ))‖ := v.le_opNorm _
      _ ≤ ‖v‖ * δ := by gcongr
  have hfi : Integrable (fun x => f x) μ :=
    _root_.BoundedContinuousFunction.integrable μ f.toBCF
  have hgi : Integrable (fun x => (g : C₀(X, ℝ)) x) μ :=
    _root_.BoundedContinuousFunction.integrable μ (g : C₀(X, ℝ)).toBCF
  have hμ_bound : |∫ x, f x ∂μ - ∫ x, (g : C₀(X, ℝ)) x ∂μ| ≤ (μ Set.univ).toReal * δ := by
    rw [show ∫ x, f x ∂μ - ∫ x, (g : C₀(X, ℝ)) x ∂μ =
      ∫ x, (f x - (g : C₀(X, ℝ)) x) ∂μ from (integral_sub hfi hgi).symm,
      show |∫ x, (f x - (g : C₀(X, ℝ)) x) ∂μ| =
        ‖∫ x, (f x - (g : C₀(X, ℝ)) x) ∂μ‖ from (Real.norm_eq_abs _).symm]
    calc ‖∫ x, (f x - (g : C₀(X, ℝ)) x) ∂μ‖
      _ ≤ ∫ x, ‖f x - (g : C₀(X, ℝ)) x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _, δ ∂μ := by
          apply integral_mono_of_nonneg
            (Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const δ)
            (Eventually.of_forall fun x => ?_)
          calc ‖f x - (g : C₀(X, ℝ)) x‖
            _ = ‖(f - (g : C₀(X, ℝ))).toBCF x‖ := rfl
            _ ≤ ‖(f - (g : C₀(X, ℝ))).toBCF‖ := BoundedContinuousFunction.norm_coe_le_norm _ x
            _ = ‖f - (g : C₀(X, ℝ))‖ := rfl
            _ ≤ δ := hg
      _ = (μ Set.univ).toReal * δ := by rw [integral_const, smul_eq_mul, Measure.real]
  have htri : |v f - ∫ x, f x ∂μ| ≤ (‖v‖ + (μ Set.univ).toReal) * δ := by
    calc |v f - ∫ x, f x ∂μ|
      _ = |(v f - v (g : C₀(X, ℝ))) + (v (g : C₀(X, ℝ)) - ∫ x, f x ∂μ)| := by ring_nf
      _ ≤ |v f - v (g : C₀(X, ℝ))| + |v (g : C₀(X, ℝ)) - ∫ x, f x ∂μ| := abs_add_le _ _
      _ = |v f - v (g : C₀(X, ℝ))| + |∫ x, f x ∂μ - v (g : C₀(X, ℝ))| := by
          congr 1; exact abs_sub_comm _ _
      _ = |v f - v (g : C₀(X, ℝ))| + |∫ x, f x ∂μ - ∫ x, (g : C₀(X, ℝ)) x ∂μ| := by rw [hcg]
      _ ≤ ‖v‖ * δ + (μ Set.univ).toReal * δ := by linarith [hv_bound, hμ_bound]
      _ = (‖v‖ + (μ Set.univ).toReal) * δ := by ring
  linarith [show |v f - ∫ x, f x ∂μ| < |v f - ∫ x, f x ∂μ| from
    calc |v f - ∫ x, f x ∂μ|
      _ ≤ (‖v‖ + (μ Set.univ).toReal) * δ := htri
      _ < C * δ := by gcongr; linarith
      _ = C * (|v f - ∫ x, f x ∂μ| / (2 * C)) := rfl
      _ = |v f - ∫ x, f x ∂μ| / 2 := by field_simp
      _ < |v f - ∫ x, f x ∂μ| := by linarith]

/-- Melrose Theorem 4.12 (Riesz representation): every continuous linear functional on
`C₀(X, ℝ)` is uniquely represented as the difference of integrals against two regular finite
Borel measures `μP - μN` on a locally compact metric space. -/
theorem riesz_representation
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (u : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ) :
    (∃ (μP μN : Measure X),
      IsFiniteMeasure μP ∧
      IsFiniteMeasure μN ∧
      μP.Regular ∧ μN.Regular ∧
      ∀ f : ZeroAtInftyContinuousMap X ℝ, u f = ∫ x, f x ∂μP - ∫ x, f x ∂μN) ∧
    (∀ (μP μN νP νN : Measure X),
      IsFiniteMeasure μP → IsFiniteMeasure μN →
      IsFiniteMeasure νP → IsFiniteMeasure νN →
      μP.Regular → μN.Regular → νP.Regular → νN.Regular →
      (∀ f : ZeroAtInftyContinuousMap X ℝ,
        ∫ x, f x ∂μP - ∫ x, f x ∂μN = ∫ x, f x ∂νP - ∫ x, f x ∂νN) →
      ∀ (E : Set X), MeasurableSet E →
        μP.real E - μN.real E = νP.real E - νN.real E) := by
  constructor
  ·

    obtain ⟨u_pos, u_neg, hu_pos_positive, hu_neg_positive, hu_decomp,
      _, _⟩ := ContinuousFunctions.dual_jordan_decomposition u

    set μP := RealRMK.rieszMeasure (restrictPositiveCLFToCc u_pos hu_pos_positive)
    set μN := RealRMK.rieszMeasure (restrictPositiveCLFToCc u_neg hu_neg_positive)

    have hμP_reg : μP.Regular := RealRMK.regular_rieszMeasure _
    have hμN_reg : μN.Regular := RealRMK.regular_rieszMeasure _
    have hμP_fin : IsFiniteMeasure μP := rieszMeasure_finite_of_positive_CLF u_pos hu_pos_positive
    have hμN_fin : IsFiniteMeasure μN := rieszMeasure_finite_of_positive_CLF u_neg hu_neg_positive
    refine ⟨μP, μN, hμP_fin, hμN_fin, hμP_reg, hμN_reg, ?_⟩


    intro f

    have hP : u_pos f = ∫ x, f x ∂μP :=
      clf_eq_integral_of_agree_on_cc u_pos μP
        (fun g => (RealRMK.integral_rieszMeasure
          (restrictPositiveCLFToCc u_pos hu_pos_positive) g).symm) f
    have hN : u_neg f = ∫ x, f x ∂μN :=
      clf_eq_integral_of_agree_on_cc u_neg μN
        (fun g => (RealRMK.integral_rieszMeasure
          (restrictPositiveCLFToCc u_neg hu_neg_positive) g).symm) f
    rw [hu_decomp]; simp only [ContinuousLinearMap.sub_apply]; linarith

  ·
    intro μP μN νP νN hμP hμN hνP hνN hμPr hμNr hνPr hνNr h E hE
    exact riesz_uniqueness μP μN νP νN h E hE

end
