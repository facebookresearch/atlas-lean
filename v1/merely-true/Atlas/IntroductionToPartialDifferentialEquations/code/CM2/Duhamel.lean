/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic

open Set MeasureTheory Filter Topology Real

noncomputable section

namespace Duhamel

/-- The squared Euclidean norm $|x|^2 = \sum_{i=1}^n (x^i)^2$ for $x \in \mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The heat kernel (fundamental solution) on $\mathbb{R}^n$:
$\Gamma_D(t, x) = \frac{1}{(4 \pi D t)^{n/2}} \exp\!\left(-\frac{|x|^2}{4 D t}\right)$. -/
def heatKernel {n : ℕ} (D : ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 / (4 * π * D * t) ^ ((n : ℝ) / 2) * exp (-(euclidNormSq x) / (4 * D * t))

/-- The spatial Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$. -/
def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- The heat operator $\partial_t u - D \Delta u$ applied to $u$ at $(t, x)$. -/
def heatOperator {n : ℕ} (D : ℝ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => u s x) t - D * laplacian (u t) x

/-- Spatial convolution $(f * g)(x) = \int_{\mathbb{R}^n} f(x - y) g(y)\, d^n y$. -/
def spatialConvolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, f (x - y) * g y

/-- Duhamel's formula: the candidate solution to the inhomogeneous heat equation
$u_t - D \Delta u = f$ with initial data $g$ is
$u(t, x) = (\Gamma_D(t, \cdot) * g)(x) + \int_0^t (\Gamma_D(t - s, \cdot) * f(s, \cdot))(x)\, ds$. -/
def duhamelSolution {n : ℕ} (D : ℝ) (g : (Fin n → ℝ) → ℝ)
    (f : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  spatialConvolution (heatKernel D t) g x +
    ∫ s in Icc 0 t, spatialConvolution (heatKernel D (t - s)) (f s) x


end Duhamel

end
