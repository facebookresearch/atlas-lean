/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped ENNReal NNReal Pointwise
open Set Metric

namespace ABCSumProduct

/-- The `δ`-covering number `|X|_δ` of a subset `X ⊆ ℝ`: the minimum number of balls of
radius `δ` needed to cover `X`. Returned as an `ℕ∞` value. -/
noncomputable def deltaCoveringNumberR (δ : ℝ) (X : Set ℝ) : ℕ∞ :=
  Metric.coveringNumber δ.toNNReal X

/-- A set `X ⊆ B(0,1) ⊂ ℝ` is `(δ, s, C)`-regular if for every ball `B(x, r)` with
`δ ≤ r ≤ 1` we have `|X ∩ B(x, r)|_δ ≤ C r^s |X|_δ`. This is the one-dimensional
δ-discretised version of the `(δ, s, C)`-set condition used in projection theory. -/
def IsDeltaRegularSetR (δ s C : ℝ) (X : Set ℝ) : Prop :=
  X ⊆ ball (0 : ℝ) 1 ∧
  ∀ (x : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
    (deltaCoveringNumberR δ (X ∩ ball x r) : ℝ≥0∞) ≤
      ENNReal.ofReal (C * r ^ s) * (deltaCoveringNumberR δ X : ℝ≥0∞)

/-- `X` has covering exponent `s` (up to a multiplicative constant `C`) at scale `δ`:
`C⁻¹ δ^{-s} ≤ |X|_δ ≤ C δ^{-s}`. This says `|X|_δ ∼ δ^{-s}`. -/
def HasCoveringExponent (δ s C : ℝ) (X : Set ℝ) : Prop :=
  ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ (deltaCoveringNumberR δ X : ℝ≥0∞) ∧
  (deltaCoveringNumberR δ X : ℝ≥0∞) ≤ ENNReal.ofReal (C * δ ^ (-s))


end ABCSumProduct
