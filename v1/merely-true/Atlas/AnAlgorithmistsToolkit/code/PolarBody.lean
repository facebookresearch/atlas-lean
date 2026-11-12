/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.Separation

open RealInnerProductSpace

namespace ConvexGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polarBody (K : Set E) : Set E :=
  { y : E | ∀ x ∈ K, ⟪y, x⟫ ≤ 1 }

theorem subset_polarBody_polarBody (K : Set E) : K ⊆ polarBody (polarBody K) := by
  intro x hx y hy
  rw [real_inner_comm]
  exact hy x hx

theorem polarBody_polarBody_eq [CompleteSpace E] {K : Set E}
    (hK_convex : Convex ℝ K) (hK_closed : IsClosed K)
    (hK_zero : (0 : E) ∈ K) :
    polarBody (polarBody K) = K := by
  apply Set.Subset.antisymm _ (subset_polarBody_polarBody K)
  intro y hy
  by_contra h
  obtain ⟨f, u, hfK, hfy⟩ := geometric_hahn_banach_closed_point hK_convex hK_closed h
  have hu_pos : 0 < u := by
    have := hfK 0 hK_zero
    simp at this
    exact this
  set v := (InnerProductSpace.toDual ℝ E).symm f
  have hfv : ∀ x : E, f x = @inner ℝ E _ v x := by
    intro x
    have heq : f = (InnerProductSpace.toDual ℝ E) v :=
      ((InnerProductSpace.toDual ℝ E).apply_symm_apply f).symm
    rw [heq, InnerProductSpace.toDual_apply_apply]
  have hvu_mem : (u⁻¹ • v) ∈ polarBody K := by
    intro x hx
    rw [inner_smul_left, RCLike.conj_to_real, ← hfv]
    rw [inv_mul_le_iff₀ hu_pos]
    linarith [hfK x hx]
  have hvu_y : @inner ℝ E _ (u⁻¹ • v) y > 1 := by
    rw [inner_smul_left, RCLike.conj_to_real, ← hfv]
    rw [show (u⁻¹ * f y > 1) ↔ (1 < u⁻¹ * f y) from gt_iff_lt]
    rw [one_lt_inv_mul₀ hu_pos]
    linarith
  have hcontra := hy (u⁻¹ • v) hvu_mem
  have := real_inner_comm (u⁻¹ • v) y
  linarith

end ConvexGeometry
