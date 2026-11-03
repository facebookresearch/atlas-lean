/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Atlas.Buildings.code.GeometricAlgebra.AnisotropicDecomposition

namespace Garrett

variable {k : Type*} [Field k]


/-- A formed space that is simultaneously anisotropic and hyperbolic must be trivial:
every vector is zero. -/
theorem anisotropic_hyperbolic_trivial
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V)
    (hAniso : BilinForm.IsAnisotropic B)
    (hHyp : BilinForm.IsHyperbolic B) :
    ∀ v : V, v = 0 := by
  obtain ⟨W, hW_iso, hW_orth, _hnd⟩ := hHyp

  have hW_bot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    exact hAniso w (hW_iso w hw w hw)

  rw [hW_bot] at hW_orth
  intro v
  have hv_in_orth : v ∈ LinearMap.BilinForm.orthogonal B ⊥ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    unfold LinearMap.BilinForm.IsOrtho
    rw [(Submodule.mem_bot k).mp hw]
    simp [map_zero]
  rw [hW_orth] at hv_in_orth
  exact (Submodule.mem_bot k).mp hv_in_orth

end Garrett
