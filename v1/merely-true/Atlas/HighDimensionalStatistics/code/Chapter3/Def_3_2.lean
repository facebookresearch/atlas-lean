/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1

set_option maxHeartbeats 1600000

open MeasureTheory

namespace Chapter3

/-- Linear combination `∑ⱼ θⱼ · φⱼ` of dictionary elements `φ₁, …, φ_M`
with weights `θ`. -/
noncomputable def dictCombination {d M : ℕ} (φ : Fin M → (Fin d → ℝ))
    (θ : Fin M → ℝ) : Fin d → ℝ :=
  ∑ j : Fin M, θ j • φ j

/-- Oracle risk over a constraint set `K` (Definition 3.2 in Rigollet):
the infimum of the risk `R(∑ⱼ θⱼ φⱼ)` over all coefficients `θ ∈ K`. -/
noncomputable def oracleRisk {d M : ℕ} (R : (Fin d → ℝ) → ℝ)
    (φ : Fin M → (Fin d → ℝ)) (K : Set (Fin M → ℝ)) : ℝ :=
  ⨅ θ ∈ K, R (dictCombination φ θ)

/-- `θbar` is an oracle for the risk `R` on `K` (Definition 3.2): it
belongs to `K` and minimizes `R(∑ⱼ θⱼ φⱼ)` over `K`. -/
def IsOracle {d M : ℕ} (R : (Fin d → ℝ) → ℝ)
    (φ : Fin M → (Fin d → ℝ)) (K : Set (Fin M → ℝ)) (θbar : Fin M → ℝ) : Prop :=
  θbar ∈ K ∧ ∀ θ ∈ K, R (dictCombination φ θbar) ≤ R (dictCombination φ θ)

/-- The estimator `fhat` satisfies an oracle inequality with constant
`C ≥ 1` and remainder `r`: in expectation, `E[R(fhat)] ≤ C · oracleRisk + r`. -/
def SatisfiesOracleInequality {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : (Fin d → ℝ) → ℝ) (φ : Fin M → (Fin d → ℝ))
    (fhat : Ω → (Fin d → ℝ)) (K : Set (Fin M → ℝ)) (C r : ℝ) : Prop :=
  C ≥ 1 ∧ ∫ ω, R (fhat ω) ∂μ ≤ C * oracleRisk R φ K + r

/-- Exact oracle inequality (`C = 1`): `E[R(fhat)] ≤ oracleRisk + r`. -/
def SatisfiesExactOracleInequality {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : (Fin d → ℝ) → ℝ) (φ : Fin M → (Fin d → ℝ))
    (fhat : Ω → (Fin d → ℝ)) (K : Set (Fin M → ℝ)) (r : ℝ) : Prop :=
  SatisfiesOracleInequality μ R φ fhat K 1 r

/-- High-probability oracle inequality: with probability at least `1 - δ`,
`R(fhat) ≤ C · oracleRisk + rem(δ)`. -/
def SatisfiesHighProbOracleInequality {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : (Fin d → ℝ) → ℝ) (φ : Fin M → (Fin d → ℝ))
    (fhat : Ω → (Fin d → ℝ)) (K : Set (Fin M → ℝ)) (C : ℝ)
    (rem : ℝ → ℝ) : Prop :=
  C ≥ 1 ∧ ∀ δ > 0,
    μ {ω | R (fhat ω) ≤ C * oracleRisk R φ K + rem δ} ≥ 1 - ENNReal.ofReal δ

end Chapter3
