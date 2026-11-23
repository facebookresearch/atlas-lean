/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace FurstenbergCorollary

/-- The "real SETUP" data for Euclidean projection theorems: a scale $R > 1$, a point
set of cardinality `X_card`, a direction set of cardinality `D_card`, a bound `S` on
$\max_{\theta\in D}|\pi_\theta(X)|$, and covering-number functions $N_X(r)$ and $N_D(\rho)$
counting balls of various radii intersecting $X$ and $D$. -/
structure RealProjectionSetup where
  R : ℝ
  hR : 1 < R
  X_card : ℕ
  hX_pos : 0 < X_card
  D_card : ℕ
  hD_pos : 0 < D_card
  S : ℕ
  hS_pos : 0 < S
  N_X : ℝ → ℕ
  N_D : ℝ → ℕ

/-- Witness that the sets $X$ and $D$ in a `RealProjectionSetup` have **Hausdorff spacing**:
there exist exponents $\alpha, \beta \in [0,1]$ and a constant $C$ such that
$|X| \sim R^\alpha$, $|D| \sim R^\beta$, $N_X(r) \lesssim r^\alpha$ for all $1 \le r \le R$,
and $N_D(\rho) \lesssim (\rho R)^\beta$ for all $R^{-1} \le \rho \le 1$. -/
structure HasHausdorffSpacing (setup : RealProjectionSetup) where
  α : ℝ
  hα_nonneg : 0 ≤ α
  hα_le_one : α ≤ 1
  β : ℝ
  hβ_nonneg : 0 ≤ β
  hβ_le_one : β ≤ 1
  C : ℝ
  hC_pos : 0 < C
  hX_size_lower : C⁻¹ * setup.R ^ α ≤ (setup.X_card : ℝ)
  hX_size_upper : (setup.X_card : ℝ) ≤ C * setup.R ^ α
  hD_size_lower : C⁻¹ * setup.R ^ β ≤ (setup.D_card : ℝ)
  hD_size_upper : (setup.D_card : ℝ) ≤ C * setup.R ^ β
  hN_X_bound : ∀ r : ℝ, 1 ≤ r → r ≤ setup.R → (setup.N_X r : ℝ) ≤ C * r ^ α
  hN_D_bound : ∀ ρ : ℝ, setup.R⁻¹ ≤ ρ → ρ ≤ 1 → (setup.N_D ρ : ℝ) ≤ C * (ρ * setup.R) ^ β


end FurstenbergCorollary
