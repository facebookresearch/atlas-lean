/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open MeasureTheory Measure Set

noncomputable section

namespace HeatUniqueness

/-- A predicate asserting that $u : [0, T] \times [0, L] \to \mathbb{R}$ is a
classical solution to the inhomogeneous heat equation
$u_t - u_{xx} = f(t, x)$ with initial condition $u(0, x) = g(x)$ and Dirichlet
boundary conditions $u(t, 0) = \alpha(t)$, $u(t, L) = \beta(t)$, together with
the regularity (continuity and differentiability) hypotheses needed for the
uniqueness argument via the energy method. -/
structure IsHeatSolution (T L : ℝ) (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (α β : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  pde : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ioo 0 L,
    deriv (u · x) t - deriv (deriv (u t ·)) x = f t x
  initial : ∀ x ∈ Icc 0 L, u 0 x = g x
  left_bc : ∀ t ∈ Icc 0 T, u t 0 = α t
  right_bc : ∀ t ∈ Icc 0 T, u t L = β t
  cont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc 0 T ×ˢ Icc 0 L)
  diffT : ∀ t ∈ Icc 0 T, ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (u · x) t
  diffX : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ (u t ·) x
  diffXX : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ (deriv (u t ·)) x
  contDerivT : ContinuousOn (fun p : ℝ × ℝ => deriv (u · p.2) p.1) (Icc 0 T ×ˢ Icc 0 L)
  diffXGlobal : ∀ t ∈ Ioo 0 T, Differentiable ℝ (u t ·)
  diffXXGlobal : ∀ t ∈ Ioo 0 T, Differentiable ℝ (deriv (u t ·))
  contDerivX : ∀ t ∈ Ioo 0 T, ContinuousOn (deriv (u t ·)) (Icc 0 L)
  contDerivXX : ∀ t ∈ Ioo 0 T, ContinuousOn (deriv (deriv (u t ·))) (Icc 0 L)

/-- The $L^2$ energy of $w(t, \cdot)$ on $[0, L]$ at time $t$:
$E(t) = \int_0^L w(t, x)^2\, dx$. Used in the energy-method uniqueness proof. -/
def energy (w : ℝ → ℝ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L, (w t x) ^ 2

end HeatUniqueness
