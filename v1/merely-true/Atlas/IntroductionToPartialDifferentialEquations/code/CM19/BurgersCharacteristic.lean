/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

/-- The defining ODE system for a characteristic curve $(\gamma_t, \gamma_x)$ of
Burger's equation $\partial_t u + u\,\partial_x u = 0$ (Definition 2.0.1):
$\tfrac{d}{ds}\gamma_t = 1$ and $\tfrac{d}{ds}\gamma_x = u(\gamma_t(s), \gamma_x(s))$. -/
structure BurgersCharacteristicCurves (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ) : Prop where
  time_deriv : ∀ s, HasDerivAt γ_t 1 s
  space_deriv : ∀ s, HasDerivAt γ_x (u (γ_t s) (γ_x s)) s

/-- Same as `BurgersCharacteristicCurves`, but packaged with a single curve
$\gamma : \mathbb{R} \to \mathbb{R} \times \mathbb{R}$ whose two components play
the role of $\gamma_t$ and $\gamma_x$. -/
structure BurgersCharacteristicPaired (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : Prop where
  time_deriv : ∀ s, HasDerivAt (fun s => (γ s).1) 1 s
  space_deriv : ∀ s, HasDerivAt (fun s => (γ s).2) (u (γ s).1 (γ s).2) s

end
