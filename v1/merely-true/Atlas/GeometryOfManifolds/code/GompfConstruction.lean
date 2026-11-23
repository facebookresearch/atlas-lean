/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Manifold

noncomputable section

namespace Gompf

/-- Local model for a Lefschetz singularity: the holomorphic map $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
def lefschetzLocalModel : ℂ × ℂ → ℂ := fun p => p.1 ^ 2 + p.2 ^ 2

/-- A Lefschetz fibration $f: M^4 \to \Sigma^2$: a smooth map between an oriented 4-manifold and
an oriented surface, a submersion away from finitely many isolated critical points, each of
which has a local quadratic model $z_1^2 + z_2^2$. -/
structure LefschetzFibration
    {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
    [Module.Oriented ℝ E_M (Fin 4)]
    {H_M : Type*} [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]
    {E_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B]
    [Module.Oriented ℝ E_B (Fin 2)]
    {H_B : Type*} [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B)
    (B : Type*) [TopologicalSpace B] [ChartedSpace H_B B]
    {E_F : Type*} [NormedAddCommGroup E_F] [NormedSpace ℝ E_F]
    {H_F : Type*} [TopologicalSpace H_F]
    (I_F : ModelWithCorners ℝ E_F H_F)
    (F : Type*) [TopologicalSpace F] [ChartedSpace H_F F]
    where
  f : M → B
  f_smooth : ContMDiff I_M I_B ⊤ f
  fiberInclusion : F → M
  fiberInclusion_smooth : ContMDiff I_F I_M ⊤ fiberInclusion
  fiberInclusion_injective : Function.Injective fiberInclusion
  dim_total : Module.finrank ℝ E_M = 4
  dim_base : Module.finrank ℝ E_B = 2
  numCriticalPoints : ℕ
  criticalPoints : Fin numCriticalPoints → M
  isCritical : ∀ i, ¬ Function.Surjective (mfderiv I_M I_B f (criticalPoints i))
  isSubmersionAway : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    Function.Surjective (mfderiv I_M I_B f x)
  criticalPoints_isolated : ∀ (i : Fin numCriticalPoints),
    ∃ (U : Set M), criticalPoints i ∈ U ∧ IsOpen U ∧
      (∀ j, criticalPoints j ∈ U → j = i)
  hasLocalQuadraticModel : ∀ (i : Fin numCriticalPoints),
    ∃ (U : Set M) (_ : IsOpen U) (_ : criticalPoints i ∈ U)
      (φ : M → ℂ × ℂ) (ψ : B → ℂ),
      (∀ x ∈ U, ψ (f x) = lefschetzLocalModel (φ x)) ∧
      φ (criticalPoints i) = (0, 0) ∧ ψ (f (criticalPoints i)) = 0

/-- Hypothesis that the fiber class is nonzero in cohomology: there exists a closed 2-form on
$M$ (a witness for $[F]$) that evaluates non-trivially on the fiber. -/
structure FiberClassNonzero
    {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
    [Module.Oriented ℝ E_M (Fin 4)]
    {H_M : Type*} [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H_M M]
    {E_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B]
    [Module.Oriented ℝ E_B (Fin 2)]
    {H_B : Type*} [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    {B : Type*} [TopologicalSpace B] [ChartedSpace H_B B]
    {E_F : Type*} [NormedAddCommGroup E_F] [NormedSpace ℝ E_F]
    {H_F : Type*} [TopologicalSpace H_F]
    {I_F : ModelWithCorners ℝ E_F H_F}
    {F : Type*} [TopologicalSpace F] [ChartedSpace H_F F]
    (lf : LefschetzFibration I_M M I_B B I_F F) where
  witnessForm : E_M → E_M [⋀^Fin 2]→L[ℝ] ℝ
  witness_closed : ∀ x : E_M, extDeriv witnessForm x = 0
  fiber_class_nonzero : ∃ y : F,
    witnessForm (I_M (chartAt H_M (lf.fiberInclusion y) (lf.fiberInclusion y))) ≠ 0

/-- A symplectic structure on a manifold $M$: a smooth, skew-symmetric, non-degenerate 2-form
$\omega$ which is also closed ($d\omega = 0$). -/
structure SymplecticStructure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  omega : M → (E →L[ℝ] E →L[ℝ] ℝ)
  skew : ∀ (x : M) (v w : E), omega x v w = -(omega x w v)
  nondegenerate : ∀ (x : M) (v : E), (∀ w : E, omega x v w = 0) → v = 0
  smooth : ContMDiff I (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) ⊤ omega
  omega_form : E → E [⋀^Fin 2]→L[ℝ] ℝ
  is_closed : ∀ x : E, extDeriv omega_form x = 0

/-- Compatibility condition stating that the fibers of the inclusion $F \hookrightarrow M$ are
symplectic submanifolds: $\omega_F = (\iota)^* \omega_M$. -/
structure FibersAreSymplectic
    {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
    {H_M : Type*} [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H_M M]
    {E_F : Type*} [NormedAddCommGroup E_F] [NormedSpace ℝ E_F]
    {H_F : Type*} [TopologicalSpace H_F]
    {I_F : ModelWithCorners ℝ E_F H_F}
    {F : Type*} [TopologicalSpace F] [ChartedSpace H_F F]
    (omega_M : SymplecticStructure I_M M)
    (omega_F : SymplecticStructure I_F F)
    (fiberInclusion : F → M)
    where
  is_pullback : ∀ (p : F) (v w : E_F),
    omega_F.omega p v w =
      omega_M.omega (fiberInclusion p)
        (mfderiv I_F I_M fiberInclusion p v)
        (mfderiv I_F I_M fiberInclusion p w)


end Gompf

end
