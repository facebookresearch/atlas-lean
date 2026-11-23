/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

open Manifold

set_option autoImplicit false


/-- Local model for a Lefschetz singularity: the holomorphic map
$\mathbb{C}^2 \to \mathbb{C},\ (z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
noncomputable def lefschetzLocalModel : ℂ × ℂ → ℂ := fun p => p.1 ^ 2 + p.2 ^ 2


/-- A Lefschetz fibration $f : M^4 \to B^2$: a smooth map with finitely many critical points,
each modeled holomorphically by $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
structure LefschetzFibrationMathlib
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M]
    (B : Type*) [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
    [IsManifold (𝓡 2) ⊤ B] where
  f : M → B
  smooth_f : ContMDiff (𝓡 4) (𝓡 2) ⊤ f
  criticalPoints : Finset M
  isCritical : ∀ x : M, x ∈ criticalPoints ↔
    ¬ Function.Surjective (mfderiv (𝓡 4) (𝓡 2) f x)
  hasLocalQuadraticModel : ∀ p ∈ criticalPoints,
    ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U)
      (φ : M → ℂ × ℂ) (ψ : B → ℂ),
      (∀ x ∈ U, ψ (f x) = lefschetzLocalModel (φ x)) ∧
      φ p = (0, 0) ∧ ψ (f p) = 0


/-- Witness data showing that the regular fiber $F \hookrightarrow M$ of a Lefschetz fibration
represents a nonzero class in $H^2(M;\mathbb{R})$, via a closed witness $2$-form. -/
structure FiberClassNonzeroMathlib
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M]
    {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
    [IsManifold (𝓡 2) ⊤ B]
    (lf : LefschetzFibrationMathlib M B) where
  F : Type*
  [topoF : TopologicalSpace F]
  [chartedF : ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
  [manifoldF : IsManifold (𝓡 2) ⊤ F]
  fiberInclusion : F → M
  smooth_inclusion : ContMDiff (𝓡 2) (𝓡 4) ⊤ fiberInclusion
  witnessForm : EuclideanSpace ℝ (Fin 4) →
    (EuclideanSpace ℝ (Fin 4)) [⋀^Fin 2]→L[ℝ] ℝ
  witness_closed : ∀ x : EuclideanSpace ℝ (Fin 4),
    extDeriv witnessForm x = 0
  fiber_class_nonzero : ∃ y : F,
    witnessForm
      (chartAt (EuclideanSpace ℝ (Fin 4)) (fiberInclusion y) (fiberInclusion y)) ≠ 0
