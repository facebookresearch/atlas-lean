/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation

open Module FiniteDimensional

namespace Garrett

/-- A totally isotropic subspace `W₁` whose dimension is at least half of `V` is
maximal: its orthogonal complement is contained in `W₁`. -/
theorem orthogonal_le_of_isotropic_of_finrank_ge
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (W₁ : Submodule k V)
    (hB_nd : B.Nondegenerate)
    (hW₁_iso : ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₁, B w₁ w₂ = 0)
    (hW₁_dim : finrank k V ≤ 2 * finrank k W₁) :
    B.orthogonal W₁ ≤ W₁ := by

  have hW₁_le_orth : W₁ ≤ B.orthogonal W₁ := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    exact hW₁_iso w hw v hv

  have h_orth_dim : finrank k (B.orthogonal W₁) = finrank k V - finrank k W₁ :=
    LinearMap.BilinForm.finrank_orthogonal hB_nd W₁

  have h_orth_le_W₁ : finrank k (B.orthogonal W₁) ≤ finrank k W₁ := by
    have hle : finrank k W₁ ≤ finrank k V := Submodule.finrank_le W₁
    omega

  have heq : W₁ = B.orthogonal W₁ :=
    Submodule.eq_of_le_of_finrank_le hW₁_le_orth h_orth_le_W₁
  rw [← heq]

/-- Variant of `orthogonal_le_of_isotropic_of_finrank_ge` taking the
orthogonal-complement form of nondegeneracy (`IsNondegenerate'`). -/
theorem orthogonal_le_of_isotropic_of_finrank_ge'
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V)
    (W₁ : Submodule k V)
    (hB_nd : BilinForm.IsNondegenerate' B)
    (hW₁_iso : ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₁, B w₁ w₂ = 0)
    (hW₁_dim : finrank k V ≤ 2 * finrank k W₁) :
    B.orthogonal W₁ ≤ W₁ :=
  orthogonal_le_of_isotropic_of_finrank_ge B W₁
    (IsNondegenerate'_to_Nondegenerate_inline hB_nd) hW₁_iso hW₁_dim

end Garrett
