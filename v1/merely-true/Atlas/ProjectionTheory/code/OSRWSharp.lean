/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.DeltaRegular

open Metric Set InnerProductSpace

namespace ProjectionTheory

/-- A `δ`-tube in $\mathbb{R}^2$, recorded by its midpoint, its direction angle, and its
width (intended to be the small parameter `δ`). The tube is a thin rectangle of length
roughly `1` and width `width`. -/
structure DeltaTube where
  midpoint : EuclideanSpace ℝ (Fin 2)
  direction : ℝ
  width : ℝ

/-- A point `p ∈ ℝ²` lies in the `δ`-tube `T` iff its components along the tube's axis
and along the normal direction satisfy $|⟨p - m, d⟩| \le 1/2$ and
$|⟨p - m, n⟩| \le \text{width}/2$, where `m` is the midpoint, `d` the unit direction,
and `n` the unit normal. -/
def DeltaTube.contains (T : DeltaTube) (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  let dir_vec := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![Real.cos T.direction, Real.sin T.direction]
  let normal_vec := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![-Real.sin T.direction, Real.cos T.direction]
  let diff := p - T.midpoint
  |⟪diff, dir_vec⟫_ℝ| ≤ (1 : ℝ) / 2 ∧ |⟪diff, normal_vec⟫_ℝ| ≤ T.width / 2

/-- A finite set of directions `Θ ⊂ ℝ` is `(δ, s, C)`-regular if for every centre `θ₀`
and every radius `r ∈ [δ, 1]`, the count of directions in the arc of radius `r` around
`θ₀` is bounded by `C r^s · |Θ|`. This is the standard Frostman/AD-regular type
condition for the set of tube directions in the OSRW setup. -/
def IsDeltaRegularDir (Θ : Finset ℝ) (δ s C : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 ≤ s ∧
  ∀ (θ₀ : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
    ((Θ.filter (fun θ => |θ - θ₀| < r)).card : ℝ) ≤ C * r ^ s * Θ.card


end ProjectionTheory
