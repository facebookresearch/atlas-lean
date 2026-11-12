/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Real Filter

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cauchy-Schwarz for exponentials.** Under a probability measure `μ`,
$\mathbb{E}[\exp((s/2)(A - B))] \le \sqrt{\mathbb{E}[\exp(sA)] \cdot \mathbb{E}[\exp(-sB)]}$,
provided both exponential moments are finite. -/
lemma exp_cauchy_schwarz_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Ω → ℝ) (s : ℝ)
    (hA_int : Integrable (fun ω => Real.exp (s * A ω)) μ)
    (hB_int : Integrable (fun ω => Real.exp (-s * B ω)) μ) :
    ∫ ω, Real.exp (s / 2 * (A ω - B ω)) ∂μ ≤
    Real.sqrt ((∫ ω, Real.exp (s * A ω) ∂μ) * (∫ ω, Real.exp (-s * B ω) ∂μ)) := by


  have hA_meas : AEStronglyMeasurable (fun ω => exp (s / 2 * A ω)) μ := by
    have : (fun ω => exp (s / 2 * A ω)) = (fun ω => Real.sqrt (exp (s * A ω))) := by
      ext ω; rw [Real.sqrt_eq_rpow, ← exp_mul]; ring_nf
    rw [this]
    exact continuous_sqrt.comp_aestronglyMeasurable hA_int.aestronglyMeasurable
  have hB_meas : AEStronglyMeasurable (fun ω => exp (-(s / 2) * B ω)) μ := by
    have : (fun ω => exp (-(s / 2) * B ω)) = (fun ω => Real.sqrt (exp (-s * B ω))) := by
      ext ω; rw [Real.sqrt_eq_rpow, ← exp_mul]; ring_nf
    rw [this]
    exact continuous_sqrt.comp_aestronglyMeasurable hB_int.aestronglyMeasurable

  have lhs_eq : (fun ω => exp (s / 2 * (A ω - B ω))) =
      (fun ω => exp (s / 2 * A ω) * exp (-(s / 2) * B ω)) := by
    ext ω; rw [← exp_add]; congr 1; ring
  rw [lhs_eq]


  have two_eq : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hfmemLp : MemLp (fun ω => exp (s / 2 * A ω)) (ENNReal.ofReal 2) μ := by
    rw [two_eq, memLp_two_iff_integrable_sq hA_meas]
    convert hA_int using 1
    ext x; rw [pow_succ, pow_one, ← exp_add]; ring_nf
  have hgmemLp : MemLp (fun ω => exp (-(s / 2) * B ω)) (ENNReal.ofReal 2) μ := by
    rw [two_eq, memLp_two_iff_integrable_sq hB_meas]
    convert hB_int using 1
    ext x; rw [pow_succ, pow_one, ← exp_add]; ring_nf

  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show HolderConjugate (2 : ℝ) 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all _ fun ω => le_of_lt (exp_pos _))
    (ae_of_all _ fun ω => le_of_lt (exp_pos _))
    hfmemLp hgmemLp

  have sq_f : (fun a => exp (s / 2 * A a) ^ (2 : ℝ)) = (fun a => exp (s * A a)) := by
    ext x; rw [← exp_mul]; congr 1; ring
  have sq_g : (fun a => exp (-(s / 2) * B a) ^ (2 : ℝ)) = (fun a => exp (-s * B a)) := by
    ext x; rw [← exp_mul]; congr 1; ring
  rw [sq_f, sq_g] at holder

  calc ∫ ω, exp (s / 2 * A ω) * exp (-(s / 2) * B ω) ∂μ
      ≤ (∫ a, exp (s * A a) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ a, exp (-s * B a) ∂μ) ^ ((1 : ℝ) / 2) := holder
    _ = Real.sqrt (∫ a, exp (s * A a) ∂μ) *
        Real.sqrt (∫ a, exp (-s * B a) ∂μ) := by
        simp_rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt ((∫ ω, exp (s * A ω) ∂μ) * (∫ ω, exp (-s * B ω) ∂μ)) := by
        rw [← Real.sqrt_mul (integral_nonneg fun ω => le_of_lt (exp_pos _))]

end
