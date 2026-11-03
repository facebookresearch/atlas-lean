/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance

namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Common-apartment instance for the isometry building: a single hyperbolic frame already
generates an apartment whose simplices include every isotropic chain, so any two simplices share
an apartment trivially. -/
noncomputable def commonIsotropicApartmentHyp
    (B : LinearMap.BilinForm k V) (n : ℕ)
    (frame : HyperbolicFrame B n) :
    CommonIsotropicApartmentHyp B n where
  find_common := by
    intro σ₁ hσ₁ σ₂ hσ₂

    refine ⟨⟨frame, { σ | (∀ W ∈ σ, IsotropicSubspace B W) ∧
      (∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁) }⟩, ?_, ?_, ?_⟩
    ·
      exact ⟨frame, rfl⟩
    ·
      exact hσ₁
    ·
      exact hσ₂

end IsometryBuilding
