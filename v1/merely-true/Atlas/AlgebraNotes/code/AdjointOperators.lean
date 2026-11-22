/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace AdjointOperators

open scoped InnerProductSpace
open LinearMap Submodule

theorem adjoint_inner_right_property {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (v w : E) :
    @inner 𝕜 _ _ (T v) w = @inner 𝕜 _ _ v (LinearMap.adjoint T w) :=
  (LinearMap.adjoint_inner_right T v w).symm

def IsNormalOperator {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) : Prop :=
  T ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ T

theorem adjoint_maps_orthogonal {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (W : Submodule 𝕜 E) (hW : ∀ w ∈ W, T w ∈ W) :
    ∀ u ∈ Wᗮ, LinearMap.adjoint T u ∈ Wᗮ := by
  intro u hu
  rw [Submodule.mem_orthogonal'] at hu ⊢
  intro w hw
  rw [LinearMap.adjoint_inner_left]
  exact hu (T w) (hW w hw)

lemma norm_apply_eq_norm_adjoint_of_normal {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hN : T ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ T) (v : E) :
    ‖T v‖ = ‖LinearMap.adjoint T v‖ := by
  have key : ⟪T v, T v⟫_𝕜 = ⟪LinearMap.adjoint T v, LinearMap.adjoint T v⟫_𝕜 := by
    rw [← LinearMap.adjoint_inner_left T v (T v)]
    rw [show (LinearMap.adjoint T) (T v) = (LinearMap.adjoint T ∘ₗ T) v from rfl, ← hN,
        show (T ∘ₗ LinearMap.adjoint T) v = T (LinearMap.adjoint T v) from rfl]
    rw [← LinearMap.adjoint_inner_right T (LinearMap.adjoint T v) v]
  have h1 : (‖T v‖ ^ 2 : ℝ) = ‖LinearMap.adjoint T v‖ ^ 2 := by
    have h := congr_arg RCLike.re key
    rw [inner_self_eq_norm_sq_to_K (𝕜 := 𝕜), inner_self_eq_norm_sq_to_K (𝕜 := 𝕜)] at h
    simpa using h
  nlinarith [norm_nonneg (T v), norm_nonneg (LinearMap.adjoint T v),
             sq_nonneg (‖T v‖ - ‖LinearMap.adjoint T v‖)]

theorem normal_adjoint_eigenvalue {𝕜 : Type*} {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (T : E →ₗ[𝕜] E) (hN : T ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ T)
    (v : E) (μ : 𝕜) (hv : T v = μ • v) :
    LinearMap.adjoint T v = (starRingEnd 𝕜 μ) • v := by
  set S := T - μ • LinearMap.id with hS_def
  have hSv : S v = 0 := by
    simp only [hS_def, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hv, sub_self]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd 𝕜 μ) • LinearMap.id := by
    simp only [hS_def, map_sub]
    congr 1
    rw [← LinearMap.star_eq_adjoint, star_smul, LinearMap.star_eq_adjoint, LinearMap.adjoint_id]
    rfl
  have hS_normal : S ∘ₗ LinearMap.adjoint S = LinearMap.adjoint S ∘ₗ S := by
    rw [hS_def, hSadj]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
               LinearMap.id_apply, map_sub, map_smul]
    have h : T (LinearMap.adjoint T x) = LinearMap.adjoint T (T x) :=
      LinearMap.ext_iff.mp hN x
    rw [h]
    simp only [smul_sub, smul_smul, mul_comm μ ((starRingEnd 𝕜) μ)]
    abel
  have hSadj_v : LinearMap.adjoint S v = 0 := by
    have h_norm := norm_apply_eq_norm_adjoint_of_normal S hS_normal v
    rw [hSv, norm_zero] at h_norm
    exact norm_eq_zero.mp h_norm.symm
  rw [hSadj] at hSadj_v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hSadj_v
  exact sub_eq_zero.mp hSadj_v

end AdjointOperators
