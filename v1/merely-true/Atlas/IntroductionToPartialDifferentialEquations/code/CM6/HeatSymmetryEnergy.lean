/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Basic

open MeasureTheory Real Filter Set
open scoped ENNReal

noncomputable section

namespace CM6

/-- Translation invariance of the heat equation expressed at the level of the
pointwise PDE relation: if $u_t - D \Delta u = 0$ everywhere, then for any
constants $A, t_0 \in \mathbb{R}$ and $x_0 \in \mathbb{R}^n$, the analogous
identity holds with $u_t, \Delta u$ evaluated at $(t - t_0, x - x_0)$ and
multiplied by $A$. -/
theorem heat_translation_invariance
    {n : ℕ} (D A t₀ : ℝ) (x₀ : Fin n → ℝ)
    (u_t Δu : ℝ → (Fin n → ℝ) → ℝ)
    (hpde : ∀ t x, u_t t x - D * Δu t x = 0) :
    ∀ t x, A * u_t (t - t₀) (x - x₀) - D * (A * Δu (t - t₀) (x - x₀)) = 0 := by
  intro t x
  have h := hpde (t - t₀) (x - x₀)
  linear_combination A * h

/-- The total thermal energy of $u$ at time $t$ (Definition 2.0.2):
$\mathcal{T}(t) = \int_{\mathbb{R}^n} u(t, x)\, d^n x$. -/
def totalThermalEnergy {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x, u t x

end CM6

end
