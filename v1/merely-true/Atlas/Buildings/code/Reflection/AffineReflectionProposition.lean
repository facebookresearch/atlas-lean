/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.AffineWeylBook

set_option maxHeartbeats 8000000

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- For an affine reflection group $W$ and a point $x ∈ E$, the linear-part homomorphism
$\mathrm{linearPartHom}$ is injective on the stabilizer of $x$: two stabilizing isometries
with the same linear part are equal. -/
theorem stabilizer_linearPart_injective (x : E) :
    ∀ w₁ ∈ W.Stabilizer x, ∀ w₂ ∈ W.Stabilizer x,
      linearPartHom w₁ = linearPartHom w₂ → w₁ = w₂ := by
  intro w₁ hw₁ w₂ hw₂ hlin

  have hw₁_fix : w₁ x = x := hw₁.2
  have hw₂_fix : w₂ x = x := hw₂.2

  suffices h_eq : w₁⁻¹ * w₂ = 1 by
    calc w₁ = w₁ * 1 := (mul_one w₁).symm
      _ = w₁ * (w₁⁻¹ * w₂) := by rw [h_eq]
      _ = w₂ := by rw [← mul_assoc, mul_inv_cancel, one_mul]

  have hker : linearPartHom (w₁⁻¹ * w₂) = 1 := by
    rw [map_mul, map_inv, hlin, inv_mul_cancel]

  have hfix : (w₁⁻¹ * w₂) x = x := by
    show w₁.symm (w₂ x) = x
    rw [hw₂_fix]
    exact w₁.injective (by rw [w₁.apply_symm_apply, hw₁_fix])


  ext y
  show (w₁⁻¹ * w₂) y = (1 : E ≃ᵃⁱ[ℝ] E) y
  set w := w₁⁻¹ * w₂
  simp only [AffineIsometryEquiv.coe_one, id_eq]

  have hvsub : w.linearIsometryEquiv (y - x) = w y - w x := by
    have h := w.toAffineIsometry.toAffineMap.linearMap_vsub y x
    simp only [vsub_eq_sub] at h; convert h

  have hid : w.linearIsometryEquiv (y - x) = y - x := by
    change (linearPartHom w) (y - x) = y - x
    rw [hker]; simp

  have hsub : w y - w x = y - x := by rw [← hvsub, hid]
  rw [hfix] at hsub
  exact sub_left_injective (G := E) (b := x) hsub

end AffineReflectionGroup
