/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
open MeasureTheory Real Finset BigOperators
open scoped ENNReal

noncomputable section

namespace HeatEquation

/-- Data for the 1-dimensional Dirichlet problem for the heat equation
on a rod of length $L$ over the time interval $[0, T]$: diffusion constant $D > 0$,
internal forcing $f(t, x)$, initial profile $g(x)$, and boundary data
$h_0(t), h_L(t)$ at $x = 0$ and $x = L$ respectively. -/
structure DirichletHeatProblem1D where
  L : ℝ
  T : ℝ
  D : ℝ
  g : ℝ → ℝ
  h₀ : ℝ → ℝ
  hL : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  hL_pos : L > 0
  hT_pos : T > 0
  hD_pos : D > 0

/-- The $m$-th Fourier sine coefficient of $f$ on $[0, 1]$:
$A_m = 2 \int_0^1 f(x) \sin(m \pi x)\, dx$. -/
def fourierSineCoeff (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  2 * ∫ x in (0:ℝ)..1, f x * sin (↑m * π * x)

/-- The $N$-th partial Fourier sine series of $f$:
$\sum_{m=1}^N A_m \sin(m \pi x)$. -/
def fourierSinePartialSum (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (Finset.range N).sum fun m =>
    fourierSineCoeff f (m + 1) * sin (↑(m + 1) * π * x)

/-- The squared $L^2([0, 1])$ norm: $\|f\|_{L^2}^2 = \int_0^1 |f(x)|^2\, dx$. -/
def L2NormSq (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, (f x) ^ 2

/-- The squared $L^2([0, 1])$ error between $f$ and its $N$-th Fourier sine partial sum. -/
def L2ErrorSq (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, (f x - fourierSinePartialSum f N x) ^ 2

/-- The $m$-th eigenvalue of $-\partial_x^2$ with Dirichlet conditions on $[0, 1]$:
$-m^2 \pi^2$. -/
def eigenvalue (m : ℕ) : ℝ := -(↑m ^ 2 * π ^ 2)



end HeatEquation

end
