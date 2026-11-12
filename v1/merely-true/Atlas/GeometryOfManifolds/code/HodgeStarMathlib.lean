/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Manifold ComplexConjugate
open MeasureTheory
set_option autoImplicit false

noncomputable section

namespace HodgeStarMathlib

/-- A smooth complex-valued $k$-form on $M$ modelled on $\mathbb{C}^n$: a pointwise alternating
$\mathbb{C}$-multilinear $k$-form on $\mathbb{C}^n$. -/
def SmoothForm (n : ℕ) (M : Type*) [TopologicalSpace M] (k : ℕ) : Type _ :=
  M → (EuclideanSpace ℂ (Fin n)) [⋀^Fin k]→L[ℂ] ℂ

/-- Pointwise additive group structure on smooth $k$-forms. -/
instance instAddCommGroupSmoothForm {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    AddCommGroup (SmoothForm n M k) := Pi.addCommGroup

/-- Pointwise $\mathbb{C}$-module structure on smooth $k$-forms. -/
instance instModuleSmoothForm {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    Module ℂ (SmoothForm n M k) := Pi.module _ _ _

/-- Bochner integral $\int_M f \, d\mu$ of a complex-valued function against a measure $\mu$. -/
def integrateScalar {M : Type*} [MeasurableSpace M] (μ : Measure M) (f : M → ℂ) : ℂ :=
  ∫ x, f x ∂μ















end HodgeStarMathlib
