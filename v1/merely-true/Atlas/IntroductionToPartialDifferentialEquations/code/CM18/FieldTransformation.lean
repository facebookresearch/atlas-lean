/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

open Finset

noncomputable section

namespace FieldTransformation

/-- A spacetime point in $\mathbb{R}^{1+n}$. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $\mathbb{R}^{1+n}$. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A spacetime metric: at each point of $\mathbb{R}^{1+n}$, a function
$m_{\mu\nu}$ on pairs of indices. -/
abbrev SpacetimeMetric (n : ℕ) := Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ

/-- The spacetime gradient of a scalar field $\varphi$:
$(\nabla \varphi)_\mu = \partial_\mu \varphi$. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) :
    Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- Component $\partial \Psi^\mu / \partial x^\nu$ of the Jacobian of a spacetime
diffeomorphism $\Psi$ at $x$. -/
def jacobianMatrix {n : ℕ} (Ψ : Spacetime n → Spacetime n) (x : Spacetime n)
    (μ ν : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun y => Ψ y μ) x (Pi.single ν 1)

/-- Transformed scalar field under a change of coordinates (Definition 2.0.6):
$\widetilde{\varphi}(\widetilde{x}) = \varphi(\Psi^{-1}(\widetilde{x}))$. -/
def transformedField {n : ℕ} (φ : ScalarField n)
    (Ψinv : Spacetime n → Spacetime n) (xt : Spacetime n) : ℝ :=
  φ (Ψinv xt)

/-- Transformed gradient of a scalar field under a change of coordinates
(Definition 2.0.6):
$\widetilde{\nabla}_\mu \widetilde{\varphi}(\widetilde{x}) = (M^{-1})_\mu{}^\alpha
\nabla_\alpha \varphi(\Psi^{-1}(\widetilde{x}))$. -/
def transformedGradient {n : ℕ} (φ : ScalarField n)
    (Ψinv : Spacetime n → Spacetime n) (xt : Spacetime n)
    (μ : Fin (n + 1)) : ℝ :=
  ∑ α : Fin (n + 1),
    jacobianMatrix Ψinv xt α μ * spacetimeGradient φ (Ψinv xt) α

/-- Transformed metric under a change of coordinates (Definition 2.0.6):
$\widetilde{m}_{\mu\nu}(\widetilde{x}) = (M^{-1})_\mu{}^\alpha (M^{-1})_\nu{}^\beta
m_{\alpha\beta}(\Psi^{-1}(\widetilde{x}))$. -/
def transformedMetric {n : ℕ} (m : SpacetimeMetric n)
    (Ψinv : Spacetime n → Spacetime n) (xt : Spacetime n)
    (μ ν : Fin (n + 1)) : ℝ :=
  ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    jacobianMatrix Ψinv xt α μ * jacobianMatrix Ψinv xt β ν *
    m (Ψinv xt) α β

/-- Transformed inverse metric under a change of coordinates (Definition 2.0.6):
$(\widetilde{m}^{-1})^{\mu\nu}(\widetilde{x}) = M_\alpha{}^\mu M_\beta{}^\nu
(m^{-1})^{\alpha\beta}(\Psi^{-1}(\widetilde{x}))$. -/
def transformedInverseMetric {n : ℕ} (mInv : SpacetimeMetric n)
    (Ψ : Spacetime n → Spacetime n) (Ψinv : Spacetime n → Spacetime n)
    (xt : Spacetime n) (μ ν : Fin (n + 1)) : ℝ :=
  let x := Ψinv xt
  ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    jacobianMatrix Ψ x μ α * jacobianMatrix Ψ x ν β * mInv x α β

end FieldTransformation
