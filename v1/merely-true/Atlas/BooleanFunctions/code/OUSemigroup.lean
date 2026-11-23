/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.GaussianSpace
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.Prod

namespace GaussianSpace

open MeasureTheory ProbabilityTheory Real ContinuousLinearMap

section GaussianSumLemma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def addSmulCLM (a b : ℝ) : (E × E) →L[ℝ] E :=
  a • (ContinuousLinearMap.fst ℝ E E) + b • (ContinuousLinearMap.snd ℝ E E)

theorem gaussian_sum_pushforward (a b c : ℝ) (habc : a ^ 2 + b ^ 2 = c ^ 2) :
    ((stdGaussian E).prod (stdGaussian E)).map (addSmulCLM a b) =
    (stdGaussian E).map (c • ContinuousLinearMap.id ℝ E) := by
  apply Measure.ext_of_charFunDual
  ext L'
  rw [charFunDual_map, charFunDual_prod]
  have h1 : (L'.comp (addSmulCLM (E := E) a b)).comp (ContinuousLinearMap.inl ℝ E E) = a • L' := by
    ext x; simp [addSmulCLM]
  have h2 : (L'.comp (addSmulCLM (E := E) a b)).comp (ContinuousLinearMap.inr ℝ E E) = b • L' := by
    ext x; simp [addSmulCLM]
  rw [h1, h2, charFunDual_stdGaussian, charFunDual_stdGaussian]
  rw [charFunDual_map]
  have h3 : L'.comp (c • ContinuousLinearMap.id ℝ E) = c • L' := by
    ext x; simp
  rw [h3, charFunDual_stdGaussian]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have ha : (|a| : ℝ) ^ 2 = a ^ 2 := sq_abs a
  have hb : (|b| : ℝ) ^ 2 = b ^ 2 := sq_abs b
  have hc : (|c| : ℝ) ^ 2 = c ^ 2 := sq_abs c
  have key : |a| ^ 2 * ‖L'‖ ^ 2 + |b| ^ 2 * ‖L'‖ ^ 2 = |c| ^ 2 * ‖L'‖ ^ 2 := by
    nlinarith
  norm_cast
  linarith

theorem integral_gaussian_sum (a b c : ℝ) (habc : a ^ 2 + b ^ 2 = c ^ 2)
    (g : E → ℝ) (hg_meas : Measurable g)
    (hg_int : Integrable (g ∘ (addSmulCLM (E := E) a b))
      ((stdGaussian E).prod (stdGaussian E))) :
    ∫ w, ∫ v, g (a • w + b • v) ∂(stdGaussian E) ∂(stdGaussian E) =
    ∫ u, g (c • u) ∂(stdGaussian E) := by
  have h_eq : ∀ w v, g (a • w + b • v) = (g ∘ (addSmulCLM (E := E) a b)) (w, v) := by
    intro w v; simp [addSmulCLM, Function.comp]
  simp_rw [h_eq]
  rw [← integral_prod _ hg_int]
  simp only [Function.comp]
  rw [← integral_map (by fun_prop : AEMeasurable (addSmulCLM (E := E) a b) _)
      hg_meas.aestronglyMeasurable]
  rw [gaussian_sum_pushforward a b c habc]
  rw [integral_map (by fun_prop : AEMeasurable (c • ContinuousLinearMap.id ℝ E) (stdGaussian E))
      hg_meas.aestronglyMeasurable]
  simp [ContinuousLinearMap.coe_smul']

end GaussianSumLemma
set_option maxHeartbeats 400000 in
theorem ornsteinUhlenbeckOp_comp {n : ℕ} (ρ σ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (hf_int : ∀ (v : EuclideanSpace ℝ (Fin n)),
      Integrable (fun u => f (v + Real.sqrt (1 - (ρ * σ) ^ 2) • u))
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    ornsteinUhlenbeckOp ρ (fun x => ornsteinUhlenbeckOp σ f x) =
    ornsteinUhlenbeckOp (ρ * σ) f := by
  funext x
  simp only [ornsteinUhlenbeckOp]

  have h_alg : ∀ w v : EuclideanSpace ℝ (Fin n),
      f (σ • (ρ • x + Real.sqrt (1 - ρ ^ 2) • w) + Real.sqrt (1 - σ ^ 2) • v) =
      f ((ρ * σ) • x + ((σ * Real.sqrt (1 - ρ ^ 2)) • w + Real.sqrt (1 - σ ^ 2) • v)) := by
    intro w v; congr 1; simp [smul_add, mul_smul, mul_comm ρ σ]; abel
  simp_rw [h_alg]

  set a := σ * Real.sqrt (1 - ρ ^ 2)
  set b := Real.sqrt (1 - σ ^ 2)
  set c := Real.sqrt (1 - (ρ * σ) ^ 2)
  set g := fun z : EuclideanSpace ℝ (Fin n) => f ((ρ * σ) • x + z)

  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  have hρσ2 : (ρ * σ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ, sq_nonneg σ]
  have habc : a ^ 2 + b ^ 2 = c ^ 2 := by
    simp only [a, b, c]
    rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - ρ ^ 2)]
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - σ ^ 2)]
    rw [show (ρ * σ) ^ 2 = ρ ^ 2 * σ ^ 2 from by ring]
    rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - ρ ^ 2 * σ ^ 2)]
    ring

  change ∫ w, ∫ v, g (a • w + b • v) ∂_ ∂_ = ∫ u, g (c • u) ∂_

  have hg_meas : Measurable g := hf.comp (measurable_const.add measurable_id)
  have hg_comp_int : Integrable (g ∘ (addSmulCLM (E := EuclideanSpace ℝ (Fin n)) a b))
      ((stdGaussian _).prod (stdGaussian _)) := by
    rw [← integrable_map_measure hg_meas.aestronglyMeasurable
      (addSmulCLM (E := EuclideanSpace ℝ (Fin n)) a b).continuous.aemeasurable,
      gaussian_sum_pushforward (E := EuclideanSpace ℝ (Fin n)) a b c habc,
      integrable_map_measure hg_meas.aestronglyMeasurable
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).continuous.aemeasurable]
    exact hf_int ((ρ * σ) • x)
  exact integral_gaussian_sum a b c habc g hg_meas hg_comp_int

end GaussianSpace
