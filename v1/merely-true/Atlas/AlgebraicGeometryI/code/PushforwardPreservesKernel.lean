/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory CategoryTheory.Limits

universe v v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

/-- The "naked" pushforward `pushforward₀ F R` of presheaves of `R`-modules along
`F : C ⥤ D` (without change of ring) is an additive functor. -/
instance pushforward₀_additive (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    (pushforward₀.{v} F R).Additive where
  map_add {_ _} _ _ := by ext X x; rfl

/-- The pushforward functor `pushforward₀ F R` preserves finite limits, computed
section-wise via the evaluation functors. -/
noncomputable instance pushforward₀_preservesFiniteLimits
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PreservesFiniteLimits (pushforward₀.{v} F R) where
  preservesFiniteLimits _ _ _ := {
    preservesLimit := fun {G} => {
      preserves := fun {c} hc =>
        ⟨evaluationJointlyReflectsLimits (G ⋙ pushforward₀ F R)
          ((pushforward₀ F R).mapCone c)
          (fun X => isLimitOfPreserves (evaluation R (F.op.obj X)) hc)⟩
    }
  }

/-- Restriction of scalars along a morphism of presheaves of rings preserves finite
limits, evaluation-by-evaluation. -/
noncomputable instance restrictScalars_preservesFiniteLimits
    {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R') :
    PreservesFiniteLimits (restrictScalars.{v} α) where
  preservesFiniteLimits _ _ _ := {
    preservesLimit := fun {G} => {
      preserves := fun {c} hc =>
        ⟨evaluationJointlyReflectsLimits
          (G ⋙ restrictScalars α)
          ((restrictScalars α).mapCone c)
          (fun X => isLimitOfPreserves (ModuleCat.restrictScalars (α.app X).hom)
            (isLimitOfPreserves (evaluation R' X) hc))⟩
    }
  }

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The full pushforward `pushforward φ` (which combines `pushforward₀` and restriction
of scalars via `φ`) is additive. -/
noncomputable instance pushforward_additive :
    (pushforward.{v} φ).Additive := by
  dsimp only [pushforward]; infer_instance

/-- The full pushforward functor `pushforward φ` on presheaves of modules preserves
finite limits, since both factors do. -/
noncomputable instance pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (pushforward.{v} φ) := by
  dsimp only [pushforward]
  exact comp_preservesFiniteLimits _ _

/-- Pushforward preserves kernels: the kernel of the pushforward of `α` is isomorphic
to the pushforward of the kernel of `α`. -/
noncomputable def pushforward_kernel_iso
    {M N : PresheafOfModules.{v} R} (α : M ⟶ N) :
    (pushforward.{v} φ).obj (kernel α) ≅ kernel ((pushforward.{v} φ).map α) :=
  PreservesKernel.iso (pushforward φ) α

/-- Compatibility of the kernel isomorphism with the kernel inclusion `ι`. -/
theorem pushforward_kernel_iso_inv_ι
    {M N : PresheafOfModules.{v} R} (α : M ⟶ N) :
    (pushforward_kernel_iso φ α).inv ≫ (pushforward.{v} φ).map (kernel.ι α) =
      kernel.ι ((pushforward.{v} φ).map α) :=
  PreservesKernel.iso_inv_ι (pushforward φ) α

end PresheafOfModules
