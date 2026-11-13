/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

/-- The **Legendre transform** (or Legendre dual) of a function `Λ : ℝᵈ → ℝ`, defined by
`Λ*(x) = sup_{λ ∈ ℝᵈ} (⟨λ, x⟩ - Λ(λ))`. This is the convex conjugate of `Λ` and appears, for
instance, as the rate function in Cramér's theorem. -/
noncomputable def legendreTransform {d : ℕ} (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ l, (⟪l, x⟫_ℝ - Λ l)
