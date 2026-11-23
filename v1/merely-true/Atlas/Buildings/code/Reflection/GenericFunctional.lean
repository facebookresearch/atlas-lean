/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.GroupTheory.CosetCover
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped InnerProductSpace
open Set

noncomputable section

/-- In a finite-dimensional real inner product space, given a finite set $S$ of nonzero
vectors there exists a generic linear functional $v$ with $⟨v, γ⟩ ≠ 0$ for every $γ ∈ S$;
this follows from the fact that $E$ is not a union of finitely many proper subspaces. -/
lemma exists_inner_ne_zero_of_finite_nonzero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Finset E) (hS : ∀ γ ∈ S, γ ≠ 0) (_hne : S.Nonempty) :
    ∃ v : E, ∀ γ ∈ S, ⟪v, γ⟫_ℝ ≠ 0 := by


  let kerMap : E → Subspace ℝ E := fun γ => LinearMap.ker (innerSL ℝ γ).toLinearMap
  let T : Finset (Subspace ℝ E) := S.image kerMap

  have hT_no_top : ⊤ ∉ T := by
    simp only [T, Finset.mem_image]
    rintro ⟨γ, hγ_mem, hγ_eq⟩
    have hγ_ne : γ ≠ 0 := hS γ hγ_mem
    have hker_ne_top : kerMap γ ≠ ⊤ := by
      intro h_top
      rw [show kerMap γ = LinearMap.ker (innerSL ℝ γ).toLinearMap from rfl,
          LinearMap.ker_eq_top] at h_top
      have : innerSL ℝ γ = 0 := ContinuousLinearMap.coe_injective h_top
      have : ‖innerSL ℝ γ‖ = 0 := by rw [this]; simp
      rw [innerSL_apply_norm] at this
      exact hγ_ne (norm_eq_zero.mp this)
    exact hker_ne_top (hγ_eq ▸ rfl)

  have hT_ne_univ : ⋃ p ∈ T, (p : Set E) ≠ Set.univ :=
    Subspace.biUnion_ne_univ_of_top_notMem hT_no_top

  obtain ⟨v, hv⟩ : ∃ v : E, v ∉ ⋃ p ∈ T, (p : Set E) := by
    by_contra h
    push_neg at h
    exact hT_ne_univ (Set.eq_univ_of_forall h)
  refine ⟨v, fun γ hγ h_eq => ?_⟩

  apply hv
  rw [Set.mem_iUnion₂]
  exact ⟨kerMap γ, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩,
    LinearMap.mem_ker.mpr (by simp [real_inner_comm v γ, h_eq])⟩
