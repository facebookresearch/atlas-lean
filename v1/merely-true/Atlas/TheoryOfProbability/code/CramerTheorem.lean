/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Atlas.TheoryOfProbability.code.LargeDeviations
import Atlas.TheoryOfProbability.code.LegendreTransform
import Atlas.TheoryOfProbability.code.MGF

open scoped ENNReal InnerProductSpace
open Filter MeasureTheory ProbabilityTheory Real Finset

/-- **Vector-valued cumulant generating function** `Λ(t) = log E[exp ⟨t, X⟩]`.

For a random vector `X : Ω → ℝᵈ`, this returns the logarithm of the moment generating
function evaluated at the dual variable `t ∈ ℝᵈ`, using the Euclidean inner product. -/
noncomputable def logMGFVec {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    (t : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ ω, exp (⟪t, X ω⟫_ℝ) ∂μ)

/-- **Law of the empirical mean** `Aₙ = (1/n) ∑_{i<n} Xᵢ` for an `ℝᵈ`-valued sample.

Pushforward of `μ` under the map `ω ↦ (1/n) ∑_{i<n} Xᵢ(ω)`. Used to state Cramér's
theorem as a large deviation principle for the sequence of empirical-mean laws. -/
noncomputable def empiricalMeanMeasureVec {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  μ.map (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω))

/-- **Cramér rate function** `Λ*(x) = sup_λ {⟨λ, x⟩ − Λ(λ)}` (Lecture 13).

The Legendre transform of the cumulant generating function `Λ = logMGFVec X μ`,
viewed as an `ℝ≥0∞`-valued rate function for the large deviation principle of the
empirical means of i.i.d. copies of `X`. -/
noncomputable def cramerRateFunction {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (legendreTransform (logMGFVec X μ) x)

