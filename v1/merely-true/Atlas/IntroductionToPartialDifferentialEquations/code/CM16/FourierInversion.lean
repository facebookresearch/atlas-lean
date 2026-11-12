/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform

open MeasureTheory Complex Finset
open scoped FourierTransform RealInnerProductSpace

set_option maxHeartbeats 400000

noncomputable section

namespace FourierAnalysis

/-- Fourier inversion theorem (Theorem 4.1), forward direction: for a continuous
$f \in L^1(\mathbb{R}^n)$ with $\hat{f} \in L^1$, the inverse Fourier transform of
$\hat{f}$ recovers $f$, i.e. $(\hat{f})^\vee = f$. -/
theorem fourier_inversion_forwardND (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf_cont : Continuous f)
    (hf : Integrable f)
    (hf_hat : Integrable (fourierTransformND n f))
    (x : Fin n → ℝ) :
    inverseFourierTransformND n (fourierTransformND n f) x = f x :=
  fourier_inversionND n f hf hf_hat hf_cont x

/-- Fourier inversion theorem (Theorem 4.1), reverse direction: for a continuous
$f \in L^1(\mathbb{R}^n)$ with $f^\vee \in L^1$, the Fourier transform of $f^\vee$
recovers $f$, i.e. $(f^\vee)^\wedge = f$. -/
theorem fourier_inversion_reverseND (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf_cont : Continuous f)
    (hf : Integrable f)
    (hf_check : Integrable (inverseFourierTransformND n f))
    (x : Fin n → ℝ) :
    fourierTransformND n (inverseFourierTransformND n f) x = f x := by

  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)

  have hg_int : Integrable g :=
    ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).mpr hf

  have hg_cont : Continuous g := hf_cont.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))

  let h : EuclideanSpace ℝ (Fin n) → ℂ := fun y => g (-y)
  have hh_int : Integrable h := hg_int.comp_neg
  have hh_cont : Continuous h := hg_cont.comp continuous_neg
  have h_fg : 𝓕 h = 𝓕⁻ g := (Real.fourierInv_eq_fourier_comp_neg g).symm

  have hFh_int : Integrable (𝓕 h) := by
    rw [h_fg]
    have h_eq : inverseFourierTransformND n f = (𝓕⁻ g) ∘ (WithLp.toLp 2) :=
      funext (fun ξ => inverseFourierTransformND_eq_fourierInv_bridge n f ξ)
    rw [h_eq] at hf_check
    exact ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding).mp hf_check

  have h_inv : ∀ v : EuclideanSpace ℝ (Fin n), 𝓕⁻ (𝓕 h) v = h v :=
    fun v => hh_int.fourierInv_fourier_eq hFh_int hh_cont.continuousAt

  rw [h_fg] at h_inv

  have h1 := h_inv (-(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))

  change 𝓕⁻ (𝓕⁻ g) (-WithLp.toLp 2 x) = g (- -WithLp.toLp 2 x) at h1
  rw [neg_neg] at h1


  rw [Real.fourierInv_eq_fourier_neg (𝓕⁻ g) (-WithLp.toLp 2 x)] at h1
  simp only [neg_neg] at h1


  rw [fourierTransformND_eq_fourier_bridge]

  have h_comp : (inverseFourierTransformND n f) ∘ @WithLp.ofLp 2 (Fin n → ℝ) = 𝓕⁻ g := by
    funext ξ
    show inverseFourierTransformND n f (WithLp.ofLp ξ) = 𝓕⁻ g ξ
    rw [inverseFourierTransformND_eq_fourierInv_bridge]
  rw [h_comp]
  exact h1

/-- Fourier inversion theorem (Theorem 4.1, combined): under the integrability
hypotheses, both $(\hat{f})^\vee = f$ and $(f^\vee)^\wedge = f$. That is, the
Fourier transform $\wedge$ and its inverse $\vee$ are mutual inverses. -/
theorem fourier_inversion_theorem (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf_cont : Continuous f)
    (hf : Integrable f)
    (hf_hat : Integrable (fourierTransformND n f))
    (hf_check : Integrable (inverseFourierTransformND n f))
    (x : Fin n → ℝ) :
    inverseFourierTransformND n (fourierTransformND n f) x = f x ∧
    fourierTransformND n (inverseFourierTransformND n f) x = f x :=
  ⟨fourier_inversion_forwardND n f hf_cont hf hf_hat x,
   fourier_inversion_reverseND n f hf_cont hf hf_check x⟩

end FourierAnalysis
