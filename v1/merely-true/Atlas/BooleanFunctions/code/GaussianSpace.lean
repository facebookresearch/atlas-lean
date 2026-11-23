/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.Polynomial.Hermite.Basic

namespace GaussianSpace

open MeasureTheory ProbabilityTheory Real

variable {n : ℕ}

noncomputable def ornsteinUhlenbeckOp1D (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (ρ * x + Real.sqrt (1 - ρ ^ 2) * z) ∂(gaussianReal 0 1)

noncomputable def ornsteinUhlenbeckOp (ρ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ w, f (ρ • x + Real.sqrt (1 - ρ ^ 2) • w)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

noncomputable def stdGaussianDensity (t : ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * Real.exp (-(t ^ 2) / 2)

theorem stdGaussianDensity_eq_gaussianPDFReal (t : ℝ) :
    stdGaussianDensity t = gaussianPDFReal 0 1 t := by
  simp only [stdGaussianDensity, gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]

theorem integral_stdGaussianDensity_eq_one :
    ∫ t : ℝ, stdGaussianDensity t = 1 := by
  have h : (fun t => stdGaussianDensity t) = gaussianPDFReal 0 1 := by
    ext t
    exact stdGaussianDensity_eq_gaussianPDFReal t
  rw [h]
  exact integral_gaussianPDFReal_eq_one 0 one_ne_zero

noncomputable def hermiteFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.hermite k).eval₂ (Int.castRingHom ℝ) x

noncomputable def hermiteFun1 (k : ℕ) (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  hermiteFun k (x 0)





end GaussianSpace
