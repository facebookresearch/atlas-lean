/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.LefschetzFibrationMathlib
import Atlas.GeometryOfManifolds.code.SymplecticManifoldMathlib

set_option autoImplicit false

open Manifold


/-- A blow-up of a smooth $4$-manifold $M$ at finitely many points, producing a new manifold
$\hat M$ together with a smooth blow-down map $\pi : \hat M \to M$. The structure records the
points blown up and the existence of local complex blow-up models around each exceptional set,
where the blow-down fails to be a submersion. -/
structure BlowupMathlib
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M]
    (Mhat : Type*) [TopologicalSpace Mhat] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Mhat]
    [IsManifold (𝓡 4) ⊤ Mhat] where
  blowdown : Mhat → M
  blowdown_smooth : ContMDiff (𝓡 4) (𝓡 4) ⊤ blowdown
  numBlowups : ℕ
  numBlowups_pos : 0 < numBlowups
  blownUpPoints : Fin numBlowups → M
  hasLocalBlowupModel : ∀ (j : Fin numBlowups),
    ∃ (U : Set M) (_ : IsOpen U) (_ : blownUpPoints j ∈ U)
      (Uhat : Set Mhat) (_ : IsOpen Uhat)
      (φ : M → ℂ × ℂ) (_φhat : Mhat → ℂ × ℂ),

      (∀ x ∈ Uhat, φ (blowdown x) = (0, 0) →
        ¬ Function.Surjective (mfderiv (𝓡 4) (𝓡 4) blowdown x)) ∧

      φ (blownUpPoints j) = (0, 0)


/-- The data witnessing that a $4$-manifold $\hat M$ admits a Lefschetz fibration to a
compact $2$-manifold $B$ (the base, which is $S^2$ for Donaldson's theorem), together with a
closed nondegenerate area form on the base. -/
structure AdmitsLefschetzFibrationToS2
    (Mhat : Type*) [TopologicalSpace Mhat] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) Mhat]
    [IsManifold (𝓡 4) ⊤ Mhat] where
  B : Type*
  [topoB : TopologicalSpace B]
  [chartedB : ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
  [manifoldB : IsManifold (𝓡 2) ⊤ B]
  [compactB : CompactSpace B]
  lf : LefschetzFibrationMathlib Mhat B
  baseAreaForm : EuclideanSpace ℝ (Fin 2) → (EuclideanSpace ℝ (Fin 2)) [⋀^Fin 2]→L[ℝ] ℝ
  baseForm_closed : ∀ x : EuclideanSpace ℝ (Fin 2), extDeriv baseAreaForm x = 0
  baseForm_nondegenerate : ∀ x : EuclideanSpace ℝ (Fin 2), baseAreaForm x ≠ 0




