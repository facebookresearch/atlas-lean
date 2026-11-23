/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.HausdorffSpacing
import Atlas.ProjectionTheory.code.OSRW
import Atlas.ProjectionTheory.code.DoubleCountingRealCor

namespace ProjectionTheory

open Finset

/-- Shorthand for the Euclidean plane `ℝ²` with its standard inner product. -/
noncomputable abbrev ℝ2 := EuclideanSpace ℝ (Fin 2)

/--
The "real `R`-SETUP" for the Euclidean version of Theorem 2.3. Bundles a scale
`R ≥ 1`, a finite point set `X ⊂ ℝ²`, a set of directions `D ⊂ ℝ` that is
`1/R`-separated, and a uniform projection bound `|π_θ(X)| ≤ S` for all `θ ∈ D`.
This is the standard hypothesis under which the Fourier-method projection
estimates are proved.
-/
structure RSetup where
  R : ℝ
  hR : 1 ≤ R
  X : Finset ℝ2
  D : Finset ℝ
  hD_sep : ∀ θ₁ ∈ D, ∀ θ₂ ∈ D, θ₁ ≠ θ₂ → |θ₁ - θ₂| ≥ 1 / R
  S : ℕ
  hS_pos : 0 < S
  hS_bound : ∀ θ ∈ D, (X.image (orthProj θ)).card ≤ S
  hX_nonempty : X.Nonempty
  hD_nonempty : D.Nonempty

end ProjectionTheory
