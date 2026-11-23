/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.GeometricAlgebra.BilinFormComplementation

namespace Garrett

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Trivial case of Witt's extension theorem: any isometry from the zero
subspace extends to the identity automorphism of `V`. -/
theorem wittExtension_bot
    (B : LinearMap.BilinForm k V)
    (_hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    (W : Submodule k V) (φ : (⊥ : Submodule k V) ≃ₗ[k] W)
    (_hφ : IsSubspaceIsometry B ⊥ W φ) :
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : (⊥ : Submodule k V), Φ (u : V) = (φ u : V)) := by
  refine ⟨LinearEquiv.refl k V, fun v₁ v₂ => rfl, fun u => ?_⟩
  simp only [LinearEquiv.refl_apply]

  have hu0 : u = 0 := Subtype.ext ((Submodule.mem_bot k).mp u.2)
  subst hu0
  simp [map_zero]

end Garrett
