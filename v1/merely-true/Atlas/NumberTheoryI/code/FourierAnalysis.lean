/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open scoped FourierTransform SchwartzMap
open MeasureTheory Complex Real

noncomputable section

namespace FourierAnalysis

abbrev SchwartzSpace := SchwartzMap ℝ ℂ

theorem fourier_schwartz_equiv :
    ∃ (Φ : SchwartzSpace ≃L[ℂ] SchwartzSpace),
      ∀ f : SchwartzSpace, (Φ f : ℝ → ℂ) = 𝓕 (f : ℝ → ℂ) :=
  ⟨FourierTransform.fourierCLE ℂ SchwartzSpace, fun f => by
    simp [FourierTransform.fourierCLE]
    rfl⟩

lemma real_inner_eq_mul (x y : ℝ) : @inner ℝ ℝ _ x y = x * y := by
  simp [inner, mul_comm]

theorem fourier_transform_scaling (f : ℝ → ℂ) (a : ℝ) (ha : 0 < a) (y : ℝ) :
    𝓕 (fun x => f (a * x)) y = (a : ℂ)⁻¹ • 𝓕 f (y / a) := by
  simp only [Real.fourier_eq, real_inner_eq_mul]
  have ha' : a ≠ 0 := ne_of_gt ha
  let g : ℝ → ℂ := fun v => (𝐞 (-(v * (y / a)))) • f v
  have hg : ∀ v, g (a * v) = (𝐞 (-(v * y))) • f (a * v) := by
    intro v; simp only [g]; congr 1; congr 1; field_simp
  simp_rw [← hg]
  rw [Measure.integral_comp_mul_left g a, abs_of_pos (inv_pos.mpr ha)]
  change (a⁻¹ : ℝ) • ∫ v, g v = ((↑a : ℂ)⁻¹) • ∫ v, (𝐞 (-(v * (y / a)))) • f v
  simp only [g, Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

theorem fderiv_fourier_eq_fourier_neg_smul (f : SchwartzSpace) :
    SchwartzMap.fderivCLM ℂ ℝ ℂ (𝓕 f) =
      𝓕 (-(2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) f) :=
  SchwartzMap.fderivCLM_fourier_eq ℂ f

theorem fourier_fderiv_eq_smul_fourier (f : SchwartzSpace) :
    𝓕 (SchwartzMap.fderivCLM ℂ ℝ ℂ f) =
      (2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) (𝓕 f) :=
  SchwartzMap.fourier_fderivCLM_eq ℂ f

theorem fourier_fderiv_interchange (f : SchwartzSpace) :
    (SchwartzMap.fderivCLM ℂ ℝ ℂ (𝓕 f) =
      𝓕 (-(2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) f)) ∧
    (𝓕 (SchwartzMap.fderivCLM ℂ ℝ ℂ f) =
      (2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) (𝓕 f)) :=
  ⟨fderiv_fourier_eq_fourier_neg_smul f, fourier_fderiv_eq_smul_fourier f⟩


theorem poisson_summation (f : SchwartzSpace) :
    ∑' n : ℤ, f n = ∑' n : ℤ, (𝓕 (⇑f)) n := by
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simp only [zero_add] at h
  rw [h]
  congr 1
  ext n
  simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one]
  rfl

abbrev mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f s

open Set Filter Asymptotics in

abbrev gammaFunction (s : ℂ) : ℂ := Complex.Gamma s

theorem euler_reflection_formula (s : ℂ) :
    Complex.Gamma s * Complex.Gamma (1 - s) =
      ↑Real.pi / Complex.sin (↑Real.pi * s) :=
  Complex.Gamma_mul_Gamma_one_sub s

end FourierAnalysis
