/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Finset Real

namespace TalagrandGeneral

variable {n : ℕ} {Ω : Fin n → Type*}

/-- The weighted Hamming distance between $x$ and $y$ with weights $α$:
$d_α(x,y) = \sum_{i : x_i \neq y_i} α_i$. -/
noncomputable def weightedHammingDist [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x y : (i : Fin n) → Ω i) : ℝ :=
  ∑ i : Fin n, if x i ≠ y i then α i else 0

/-- The weighted Hamming distance from $x$ to a set $A$:
$d_α(x,A) = \inf_{y \in A} d_α(x,y)$. -/
noncomputable def weightedHammingDistSet [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  ⨅ y ∈ A, weightedHammingDist α x y

/-- Talagrand's convex distance from $x$ to $A$:
$d_T(x,A) = \sup_{α \geq 0,\ \|α\|_2 = 1} d_α(x,A)$. -/
noncomputable def talagrandConvexDist [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  ⨆ α ∈ {α : Fin n → ℝ | (∀ i, 0 ≤ α i) ∧ ∑ i, α i ^ 2 = 1},
    weightedHammingDistSet α x A

end TalagrandGeneral

