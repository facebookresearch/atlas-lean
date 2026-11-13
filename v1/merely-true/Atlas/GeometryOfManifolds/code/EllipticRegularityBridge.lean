/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

namespace EllipticRegularityBridge


/-- Differential $k$-form on $\mathbb{R}^n$: a pointwise alternating $\mathbb{R}$-multilinear
$k$-form on $\mathbb{R}^n$. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

/-- Pointwise additive group structure on differential $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on differential $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

/-- Borel measurable space structure on $\mathbb{R}^n$, needed for integration of forms. -/
noncomputable instance instMeasurableSpace (n : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

/-- A differential form $\xi$ is smooth iff it is $C^\infty$ as a map between normed spaces. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ

/-- Abstract data of Sobolev norms $\|\xi\|_{H^s}$ on $(k+1)$-forms, indexed by regularity $s$,
required to be nonnegative. -/
structure SobolevNorms (n k : ℕ) where
  norm : ℕ → DiffForm n (k + 1) → ℝ
  norm_nonneg : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)), 0 ≤ norm s ξ

/-- $\xi$ has Sobolev regularity $H^s$ iff $\|\xi\|_{H^s} < \infty$. -/
def HasSobolevRegularity {n k : ℕ} (snorms : SobolevNorms n k) (s : ℕ)
    (ξ : DiffForm n (k + 1)) : Prop :=
  ∃ (C : ℝ), snorms.norm s ξ ≤ C


/-- A differential form on $\mathbb{R}^n$ is smooth iff it is $C^\infty$ as a manifold map between
the trivially-charted vector spaces. -/
theorem isSmoothForm_iff_contMDiff {n k : ℕ} (ξ : DiffForm n k) :
    IsSmoothForm ξ ↔
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ :=
  contMDiff_iff_contDiff.symm

/-- Forward direction: a smooth form is $C^\infty$ in the manifold sense. -/
theorem IsSmoothForm.toContMDiff {n k : ℕ} {ξ : DiffForm n k} (h : IsSmoothForm ξ) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ :=
  (isSmoothForm_iff_contMDiff ξ).mp h

/-- Reverse direction: a manifold-$C^\infty$ form is smooth in the analytic sense. -/
theorem IsSmoothForm.ofContMDiff {n k : ℕ} {ξ : DiffForm n k}
    (h : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ) :
    IsSmoothForm ξ :=
  (isSmoothForm_iff_contMDiff ξ).mpr h






end EllipticRegularityBridge
