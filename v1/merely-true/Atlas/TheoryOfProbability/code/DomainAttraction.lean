/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

noncomputable section

/-- Convolution of two measures on `ℝ`: the pushforward of the product measure `μ.prod ν`
under the addition map `(x, y) ↦ x + y`. -/
def measureConv (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)

/-- The `n`-fold convolution power of a measure `ν` on `ℝ`. By convention `convPow ν 0`
is the Dirac mass at `0` and `convPow ν (n+1) = (convPow ν n) ∗ ν`. -/
def convPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => measureConv (convPow ν n) ν

namespace ProbabilityTheory

/-- `L : ℝ → ℝ` is *slowly varying* (at infinity) if it is positive on `(0, ∞)` and
`L(cx) / L(x) → 1` as `x → ∞` for every `c > 0`. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → 0 < L x) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- `f` is *regularly varying* with index `ρ` if it can be written as `f x = x^ρ · L x`
eventually as `x → ∞`, where `L` is slowly varying. -/
def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∃ L : ℝ → ℝ, IsSlowlyVarying L ∧ ∀ᶠ x in atTop, f x = x ^ ρ * L x

/-- The right tail probability `μ((x, ∞))` as a real number. -/
def rightTail (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Ioi x)).toReal

/-- The left tail probability `μ((-∞, -x])` as a real number. -/
def leftTail (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Iic (-x))).toReal

/-- The two-sided tail `μ(|X| > x)` written as the sum of the right and left tails. -/
def combinedTail (μ : Measure ℝ) (x : ℝ) : ℝ := rightTail μ x + leftTail μ x

/-- A probability measure `μ` on `ℝ` is *stable* with index `α ∈ (0, 2]` if for every
`n > 0` there exist constants `aₙ > 0` and `bₙ` such that the `n`-fold convolution
`μ * μ * ⋯ * μ` equals the pushforward of `μ` under the affine map `x ↦ aₙ x + bₙ`. -/
def IsStable (μ : Measure ℝ) (α : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  0 < α ∧ α ≤ 2 ∧
  ∀ (n : ℕ), 0 < n →
    ∃ (aₙ : ℝ) (bₙ : ℝ), 0 < aₙ ∧
      convPow μ n = Measure.map (fun x => aₙ * x + bₙ) μ

/-- A measure `μ` on `ℝ` is *nondegenerate* if it is not a point mass `δ_a` for any `a`. -/
def IsNondegenerate (μ : Measure ℝ) : Prop :=
  ¬ ∃ a : ℝ, μ = Measure.dirac a

/-- The probability measure `μ` is *in the domain of attraction* of `G` if there exist
sequences of normalizing constants `a n > 0` and centering constants `b n` such that
the law of `(S_n - b n) / a n` (where `S_n` has law `μ^{*n}`) converges weakly to `G`,
expressed here as integration against arbitrary bounded continuous functions. -/
def InDomainOfAttraction (μ : Measure ℝ) (G : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure G ∧
  ∃ (a : ℕ → ℝ) (b : ℕ → ℝ),
    (∀ n, 0 < a n) ∧
    ∀ (f : ℝ →ᵇ ℝ),
      Tendsto
        (fun n => ∫ x, f x ∂(Measure.map (fun y => (y - b n) / a n) (convPow μ n)))
        atTop (𝓝 (∫ x, f x ∂G))

/-- `μ` has *tail balance* with parameter `p ∈ [0, 1]` if the ratio of the right tail to
the combined two-sided tail tends to `p` as `x → ∞`, i.e. `P(X > x) / P(|X| > x) → p`. -/
def HasTailBalance (μ : Measure ℝ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
  Tendsto (fun x => rightTail μ x / combinedTail μ x) atTop (𝓝 p)


/-- `μ` is in the domain of attraction of index `α` if there exists a stable law `G` of
index `α` such that `μ` is in the domain of attraction of `G`. -/
def InDomainOfAttractionIndex (μ : Measure ℝ) (α : ℝ) : Prop :=
  ∃ G : Measure ℝ, IsStable G α ∧ InDomainOfAttraction μ G





end ProbabilityTheory

