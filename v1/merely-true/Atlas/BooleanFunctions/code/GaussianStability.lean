/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace GaussianStability

variable {n : ℕ}

def gaussianSpace (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

structure IsRhoCorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (ρ : ℝ) : Prop where
  rho_mem : ρ ∈ Set.Icc (-1 : ℝ) 1
  hX_meas : Measurable X
  hY_meas : Measurable Y
  hX_dist : μ.map X = gaussianReal 0 1
  hY_dist : μ.map Y = gaussianReal 0 1
  hXY_corr : ∫ ω, X ω * Y ω ∂μ = ρ

def rhoCorrelatedGaussian (ρ : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    (fun p : ℝ × ℝ => (p.1, ρ * p.1 + Real.sqrt (1 - ρ ^ 2) * p.2))

def gaussianNoiseOperator (ρ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ w, f (ρ • z + Real.sqrt (1 - ρ ^ 2) • w)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

def gaussianNoiseStability (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, f x * gaussianNoiseOperator ρ f x
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

end GaussianStability

end
