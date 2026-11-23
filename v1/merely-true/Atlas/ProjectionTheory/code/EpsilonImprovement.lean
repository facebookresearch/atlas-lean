/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.Submultiplicative
import Mathlib
namespace ProjectionTheory

/-- Abstract data packaging the projective AD-regular projection configurations indexed
by parameters `s, t` and scale `δ`, together with a nonnegative, uniformly bounded
"ratio" functional whose supremum defines `R_{AD, proj}(s, t, δ)`. -/
structure ProjConfigDataST where
  Config : ℝ → ℝ → ℝ → Type
  ratio : (s t δ : ℝ) → Config s t δ → ℝ
  ratio_nonneg : ∀ (s t δ : ℝ) (c : Config s t δ), 0 ≤ ratio s t δ c
  ratio_bddAbove : ∀ (s t δ : ℝ), BddAbove (Set.range (ratio s t δ))
  config_nonempty : ∀ (s t δ : ℝ), Nonempty (Config s t δ)

end ProjectionTheory
