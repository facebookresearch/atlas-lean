/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open MeasureTheory Real Matrix Equiv Finset

namespace Approximation

def IsApprox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q' : Ω → ℝ) (Q ε δ : ℝ) : Prop :=
  μ {ω | |Q' ω - Q| ≤ ε * Q} ≥ ENNReal.ofReal (1 - δ)

def IsPolyTime (runtime : ℕ → ℝ → ℝ → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    (runtime n ε δ : ℝ) ≤ ↑c * (↑n + 1 / ε + Real.log (1 / δ)) ^ k

structure FPRAS where
  Ω : ℕ → ℝ → ℝ → Type*
  meas : ∀ n ε δ, MeasurableSpace (Ω n ε δ)
  μ : ∀ n ε δ, @Measure (Ω n ε δ) (meas n ε δ)
  Q : ℕ → ℝ
  estimator : ∀ n ε δ, Ω n ε δ → ℝ
  runtime : ℕ → ℝ → ℝ → ℕ
  approx : ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    @IsApprox _ (meas n ε δ) (μ n ε δ) (estimator n ε δ) (Q n) ε δ
  poly_time : IsPolyTime runtime

end Approximation
