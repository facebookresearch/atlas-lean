/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Basic

open scoped ENNReal
open Filter MeasureTheory

variable {X : Type*} [TopologicalSpace X]

/-- A **rate function** `I : X → [0, ∞]` is, by definition, a lower-semicontinuous function.
This is the basic regularity hypothesis used in the formulation of a large deviation principle. -/
structure IsRateFunction (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I

/-- A **good rate function** is a rate function whose sub-level sets `{x | I x ≤ a}` are all
compact. Goodness ensures that the variational problems `inf_{x ∈ Γ} I(x)` are attained. -/
structure IsGoodRateFunction (I : X → ℝ≥0∞) : Prop extends IsRateFunction I where
  isCompact_levelSet : ∀ a : ℝ≥0∞, IsCompact {x | I x ≤ a}

/-- A **convex rate function** on a real vector space is a rate function `I` that is convex:
`I(ax + by) ≤ a · I(x) + b · I(y)` for all `x, y ∈ X` and all weights `a, b ≥ 0` with `a + b = 1`. -/
structure IsConvexRateFunction [AddCommMonoid X] [Module ℝ X]
    (I : X → ℝ≥0∞) : Prop extends IsRateFunction I where
  convex : ∀ ⦃x y : X⦄, ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    I (a • x + b • y) ≤ ENNReal.ofReal a * I x + ENNReal.ofReal b * I y

/-- A sequence of measures `μ : ℕ → Measure X` **satisfies the large deviation principle** with
rate function `I : X → [0, ∞]` and speed `n` if `I` is a rate function and the following
asymptotic bounds hold for every Borel set `Γ ⊆ X`:
`-inf_{x ∈ Γ°} I(x) ≤ liminf (1/n) log μ_n(Γ) ≤ limsup (1/n) log μ_n(Γ) ≤ -inf_{x ∈ Γ̄} I(x)`.
Concretely, this is encoded as the standard pair of bounds: a `liminf` lower bound over open
sets `U` and a `limsup` upper bound over closed sets `F`. -/
structure SatisfiesLDP [MeasurableSpace X] (μ : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  isRateFunction : IsRateFunction I
  lower_bound : ∀ U : Set X, IsOpen U →
    - (⨅ x ∈ U, (I x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n F)) atTop ≤
      - (⨅ x ∈ F, (I x : EReal))
