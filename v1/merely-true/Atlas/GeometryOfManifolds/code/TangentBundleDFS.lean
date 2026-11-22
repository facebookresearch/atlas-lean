/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Atlas.GeometryOfManifolds.code.CompatibleComplexStructures

set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- Typeclass packaging a manifold $M$ with a pointwise tangent space $T_x M$ and the bridge
between abstract $2$-forms in `Ω 2` and their pointwise bilinear evaluations $\Omega_x$; also
records how an almost complex structure lifts to vector fields and interacts with symplectic
forms (compatibility, taming, $J^2 = -\mathrm{id}$). -/
class HasTangentSpaces (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  M : Type*
  TangentSpaceAt : M → Type*
  [instACG : ∀ x, AddCommGroup (TangentSpaceAt x)]
  [instMod : ∀ x, Module ℝ (TangentSpaceAt x)]
  [instFD : ∀ x, FiniteDimensional ℝ (TangentSpaceAt x)]
  eval₂ : ∀ (x : M), Ω 2 → LinearMap.BilinForm ℝ (TangentSpaceAt x)
  eval₂_add : ∀ (x : M) (α β : Ω 2), eval₂ x (α + β) = eval₂ x α + eval₂ x β
  eval₂_smul : ∀ (x : M) (r : ℝ) (α : Ω 2), eval₂ x (r • α) = r • eval₂ x α
  eval_is_symplectic :
    ∀ (S : SymplecticManifold Ω VF) (x : M),
      IsSymplecticForm (eval₂ x S.ω)
  liftJ : (∀ x : M, TangentSpaceAt x →ₗ[ℝ] TangentSpaceAt x) → (VF → VF)
  lift_sq_neg :
    ∀ (Jfam : ∀ x : M, TangentSpaceAt x →ₗ[ℝ] TangentSpaceAt x),
      (∀ x, IsComplexStructure (Jfam x)) →
      ∀ (X : VF) (α : Ω 1),
        inst.ι (liftJ Jfam (liftJ Jfam X)) α = -(inst.ι X α)
  lift_preserves :
    ∀ (S : SymplecticManifold Ω VF)
      (Jfam : ∀ x : M, TangentSpaceAt x →ₗ[ℝ] TangentSpaceAt x),
      (∀ x u v, (eval₂ x S.ω) ((Jfam x) u) ((Jfam x) v) =
                 (eval₂ x S.ω) u v) →
      ∀ (u v : VF),
        inst.ι (liftJ Jfam u) (inst.ι (liftJ Jfam v) S.ω) =
        inst.ι u (inst.ι v S.ω)
  lift_taming :
    ∀ (S : SymplecticManifold Ω VF)
      (Jfam : ∀ x : M, TangentSpaceAt x →ₗ[ℝ] TangentSpaceAt x),
      (∀ x (v : TangentSpaceAt x), v ≠ 0 →
        (eval₂ x S.ω) v ((Jfam x) v) > 0) →
      Function.Injective (fun (v : VF) => inst.ι (liftJ Jfam v) S.ω)

attribute [reducible, instance] HasTangentSpaces.instACG
  HasTangentSpaces.instMod
attribute [instance] HasTangentSpaces.instFD
