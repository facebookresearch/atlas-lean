/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped SchwartzMap FourierTransform
open MeasureTheory

noncomputable section

namespace FourierDistributions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Defining identity for the Fourier transform of a tempered distribution: `(𝓕 u)(φ) = u(𝓕 φ)`,
where the right-hand side uses the Fourier transform on Schwartz functions. -/
theorem fourierDistrib_apply (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    (𝓕 u) φ = u (𝓕 φ) := rfl

/-- The Fourier transform on tempered distributions, packaged as a continuous linear
equivalence of `𝓢'(V, ℂ)` with itself. -/
def fourierTempDistribCLE : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ) :=
  FourierTransform.fourierCLE ℂ 𝓢'(V, ℂ)

/-- Existence of the Fourier isomorphism on tempered distributions: there is a continuous
linear equivalence `𝓢' ≃L[ℂ] 𝓢'` that agrees with `𝓕` on distributions and whose inverse is
the inverse Fourier transform `𝓕⁻`. -/
theorem fourier_tempDistrib_isomorphism :
    ∃ e : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ),
      (∀ u, e u = 𝓕 u) ∧ (∀ u, e.symm u = 𝓕⁻ u) :=
  ⟨fourierTempDistribCLE,
    fun u => FourierTransform.fourierCLE_apply u,
    fun u => FourierTransform.fourierCLE_symm_apply u⟩

/-- The Fourier CLE coincides with the standard Fourier transform `𝓕` of tempered
distributions. -/
@[simp]
theorem fourierTempDistribCLE_apply (u : 𝓢'(V, ℂ)) :
    fourierTempDistribCLE u = 𝓕 u :=
  FourierTransform.fourierCLE_apply u

/-- The inverse of the Fourier CLE coincides with the inverse Fourier transform `𝓕⁻` of
tempered distributions. -/
@[simp]
theorem fourierTempDistribCLE_symm_apply (u : 𝓢'(V, ℂ)) :
    fourierTempDistribCLE.symm u = 𝓕⁻ u :=
  FourierTransform.fourierCLE_symm_apply u

open TemperedDistribution LineDeriv

/-- Fourier-derivative exchange (first order): the Fourier transform converts the directional
derivative `∂_m u` into multiplication by `2πi ⟨·, m⟩` of `𝓕 u`. -/
theorem fourier_lineDeriv_eq (u : 𝓢'(V, ℂ)) (m : V) :
    𝓕 (∂_{m} u) = (2 * Real.pi * Complex.I) • smulLeftCLM ℂ (inner ℝ · m) (𝓕 u) :=
  TemperedDistribution.fourier_lineDerivOp_eq u m

/-- Derivative-of-Fourier transform identity: differentiating `𝓕 u` in the direction `m`
corresponds to taking the Fourier transform of `-2πi ⟨·, m⟩ · u`. -/
theorem lineDeriv_fourier_eq (u : 𝓢'(V, ℂ)) (m : V) :
    ∂_{m} (𝓕 u) = 𝓕 (-(2 * Real.pi * Complex.I) • smulLeftCLM ℂ (inner ℝ · m) u) :=
  TemperedDistribution.lineDerivOp_fourier_eq u m

/-- Iterated multiplication by linear functionals: for a tuple `m : Fin n → V`, the operator
`iteratedMulOp m` multiplies a tempered distribution by `∏ ⟨·, m i⟩`. Defined by recursion. -/
def iteratedMulOp : {n : ℕ} → (Fin n → V) → 𝓢'(V, ℂ) → 𝓢'(V, ℂ)
  | 0, _, u => u
  | _ + 1, m, u => smulLeftCLM ℂ (inner ℝ · (m 0)) (iteratedMulOp (Fin.tail m) u)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The empty iterated multiplication operator is the identity on tempered distributions. -/
@[simp]
theorem iteratedMulOp_zero (m : Fin 0 → V) (u : 𝓢'(V, ℂ)) :
    iteratedMulOp m u = u := rfl

/-- Higher-order Fourier-derivative exchange: for any multi-index `m : Fin n → V`,
`𝓕 (∂^{m} u) = (2πi)^n · iteratedMulOp m (𝓕 u)`, generalising the first-order identity. -/
theorem fourier_iteratedLineDerivOp_eq (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V) :
    𝓕 (∂^{m} u) = (2 * Real.pi * Complex.I) ^ n • iteratedMulOp m (𝓕 u) := by
  induction n with
  | zero => simp [iteratedLineDerivOp_fin_zero, iteratedMulOp]
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, TemperedDistribution.fourier_lineDerivOp_eq,
      IH (Fin.tail m)]
    simp only [iteratedMulOp, map_smul, smul_smul, pow_succ]
    ring_nf

/-- Higher-order multi-derivative-of-Fourier identity:
`∂^{m} (𝓕 u) = 𝓕 ((-2πi)^n · iteratedMulOp m u)`. -/
theorem iteratedLineDerivOp_fourier_eq (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V) :
    ∂^{m} (𝓕 u) = 𝓕 ((-(2 * Real.pi * Complex.I)) ^ n • iteratedMulOp m u) := by
  induction n with
  | zero => simp [iteratedLineDerivOp_fin_zero, iteratedMulOp]
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, IH (Fin.tail m),
      TemperedDistribution.lineDerivOp_fourier_eq]
    simp only [iteratedMulOp, map_smul, smul_smul, pow_succ]
    ring_nf

/-- Packaged statement of the Fourier–tempered-distribution exchange: the Fourier isomorphism
on `𝓢'` together with the multi-index versions of the differentiation–multiplication
correspondence. -/
theorem fourier_tempDistrib_multiindex_exchange :
    (∃ e : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ),
      (∀ u, e u = 𝓕 u) ∧ (∀ u, e.symm u = 𝓕⁻ u)) ∧
    (∀ (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V),
      𝓕 (∂^{m} u) = (2 * Real.pi * Complex.I) ^ n • iteratedMulOp m (𝓕 u)) ∧
    (∀ (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V),
      ∂^{m} (𝓕 u) = 𝓕 ((-(2 * Real.pi * Complex.I)) ^ n • iteratedMulOp m u)) :=
  ⟨fourier_tempDistrib_isomorphism, fourier_iteratedLineDerivOp_eq,
   iteratedLineDerivOp_fourier_eq⟩

end FourierDistributions

end
