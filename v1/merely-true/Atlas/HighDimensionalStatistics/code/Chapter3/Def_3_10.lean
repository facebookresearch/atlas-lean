/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.HighDimensionalStatistics.code.Chapter3.Ex_3_8

open MeasureTheory Set

namespace Chapter3

/-- Sobolev coefficient `aⱼ(β)` used in the definition of the Sobolev
ellipsoid: equals `j^β` when `j` is even and `(j-1)^β` when `j` is odd. -/
noncomputable def sobolevCoeff (β : ℝ) (j : ℕ) : ℝ :=
  if j % 2 = 0 then (j : ℝ) ^ β else ((j - 1 : ℕ) : ℝ) ^ β

/-- Truncated Sobolev ellipsoid of smoothness `β` and radius `Q` in
dimension `M`: the set of coefficient vectors `θ` with
`∑ⱼ aⱼ(β)² θⱼ² ≤ Q`. -/
def SobolevEllipsoid (β Q : ℝ) (M : ℕ) : Set (Fin M → ℝ) :=
  {θ | ∑ j : Fin M, (sobolevCoeff β (j.val + 1))^2 * (θ j)^2 ≤ Q}

/-- The Sobolev coefficient `aⱼ(β)` is non-negative for `β ≥ 0`. -/
theorem sobolevCoeff_nonneg {β : ℝ} (_hβ : 0 ≤ β) (j : ℕ) :
    0 ≤ sobolevCoeff β j := by
  unfold sobolevCoeff
  split
  · exact Real.rpow_nonneg (Nat.cast_nonneg j) β
  · exact Real.rpow_nonneg (Nat.cast_nonneg (j - 1)) β

/-- The first Sobolev coefficient vanishes: `a₁(β) = 0` (since the constant
basis function carries no smoothness penalty). -/
theorem sobolevCoeff_one {β : ℝ} (hβ : β ≠ 0) : sobolevCoeff β 1 = 0 := by
  unfold sobolevCoeff
  simp [Real.zero_rpow hβ]

/-- Sobolev class `W(β, L)` of periodic functions on `[0,1]`: square
integrable, with absolutely continuous `(β-1)`-th derivative, square
integrable `β`-th derivative bounded in `L²` norm by `L`, and with
matching derivatives at the endpoints up to order `β - 1`. -/
def SobolevClassFn (β : ℕ) (L : ℝ) : Set (ℝ → ℝ) :=
  { f | IntegrableOn (fun x => (f x) ^ 2) (Icc 0 1) ∧
        AbsolutelyContinuousOnInterval (iteratedDeriv (β - 1) f) 0 1 ∧
        IntegrableOn (fun x => (iteratedDeriv β f x) ^ 2) (Icc 0 1) ∧
        (∀ j : Fin β, iteratedDeriv (↑j) f 0 = iteratedDeriv (↑j) f 1) ∧
        ∫ x in Icc (0 : ℝ) 1, (iteratedDeriv β f x) ^ 2 ≤ L ^ 2 }

/-- Fourier coefficient of the `j`-th derivative of `f` against the `k`-th
element of the trigonometric basis on `[0,1]`. -/
noncomputable def derivFourierCoeff (f : ℝ → ℝ) (j : ℕ) (k : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, iteratedDeriv j f x * trigBasis k x

end Chapter3
