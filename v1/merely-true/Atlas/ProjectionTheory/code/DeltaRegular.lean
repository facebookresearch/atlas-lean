/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped ENNReal NNReal
open Metric Set

namespace DeltaRegular

variable {d : ℕ}

/--
The `δ`-covering number `|X|_δ` of a set `X ⊆ ℝ^d`: the minimal number of
`δ`-balls (with centers in the ambient space) needed to cover `X`.
-/
noncomputable def deltaCoveringNumber (δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) : ℕ∞ :=
  Metric.externalCoveringNumber δ.toNNReal X

/--
A subset `E` of the unit ball in `ℝ^d` is a `(δ, s, C)`-set if for every ball
`B(x, r)` of radius `r ≥ δ`, the covering number satisfies
`|E ∩ B(x, r)|_δ ≤ C r^s |E|_δ`. This is the standard discretized notion of an
`s`-dimensional set used throughout discretized projection theory.
-/
def IsDeltaSRegular (δ s C : ℝ) (E : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  E ⊆ Metric.ball 0 1 ∧
  ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ),
    δ ≤ r → r ≤ 1 →
    (deltaCoveringNumber δ (E ∩ Metric.ball x r) : ℝ≥0∞) ≤
      ENNReal.ofReal (C * r ^ s) * (deltaCoveringNumber δ E : ℝ≥0∞)

end DeltaRegular
