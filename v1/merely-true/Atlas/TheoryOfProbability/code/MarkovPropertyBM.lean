/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith.NNRealPreprocessor

open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped NNReal ENNReal

noncomputable section

namespace BrownianMotion

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `IsBrownianMotion B ℱ μ` asserts that the family `B : ℝ≥0 → Ω → E` is a `d`-dimensional
Brownian motion under `μ` adapted to the filtration `ℱ`. It packages the standard defining
properties: `B 0 = 0` almost surely, independent increments with respect to the filtration,
adaptedness, almost-sure continuous paths, and measurability of each increment. -/
structure IsBrownianMotion (B : ℝ≥0 → Ω → E) (ℱ : Filtration ℝ≥0 m) (μ : Measure Ω) : Prop where
  zero : ∀ᵐ ω ∂μ, B 0 ω = 0
  indep_increment : ∀ (s t : ℝ≥0), s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  adapted : ∀ (t : ℝ≥0), Measurable[ℱ t] (B t)
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)
  meas_increment : ∀ (s t : ℝ≥0), s ≤ t → Measurable (fun ω => B t ω - B s ω)

/-- The time-shifted path of a Brownian motion: `shiftPath B s ω` is the function
`t ↦ B (s + t) ω`, i.e. the path of `B` starting from time `s` instead of `0`. -/
def shiftPath (B : ℝ≥0 → Ω → E) (s : ℝ≥0) : Ω → (ℝ≥0 → E) :=
  fun ω t => B (s + t) ω

/-- The law on path space of the centered shifted path `t ↦ B (s + t) ω - B s ω`. By
independence and stationarity of Brownian increments, this measure does not depend on `s`
and equals the law of standard Brownian motion. -/
def shiftedPathLaw (B : ℝ≥0 → Ω → E) (μ : Measure Ω) (s : ℝ≥0) :
    Measure (ℝ≥0 → E) :=
  Measure.map (fun ω t => B (s + t) ω - B s ω) μ

/-- The expectation of a path functional `Y` under the law of Brownian motion started from
the point `x ∈ E`. Operationally, it integrates `Y (t ↦ x + f t)` against the law of the
centered shifted path `f`. This is the function `φ(x) = E_x Y` that appears as the
conditional expectation in the Markov property. -/
def pathExpectation (B : ℝ≥0 → Ω → E) (μ : Measure Ω) (s : ℝ≥0)
    (Y : (ℝ≥0 → E) → ℝ) (x : E) : ℝ :=
  ∫ f, Y (fun t => x + f t) ∂(shiftedPathLaw B μ s)



end BrownianMotion
