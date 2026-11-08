/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ContinuousRep
import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.SmoothVectorsProps
import Atlas.LieGroups.code.SchurLemma

universe uF

noncomputable section

open scoped ComplexOrder Manifold

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def IsAdmissible (π : ContinuousRep G V) (K : Subgroup G) : Prop :=
  ∀ (Wσ : Type*) [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ), σ.IsIrreducible →
    FiniteDimensional ℂ (π.IsotypicComponent K σ)

end ContinuousRep

theorem ContinuousLinearMap.continuous_symm_of_bijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    Continuous (LinearEquiv.ofBijective f.toLinearMap hf).symm :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap.continuous_of_finiteDimensional

def ContinuousLinearMap.continuousLinearEquivOfBijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    V₁ ≃L[ℂ] V₂ := by
  let linEquiv : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective f.toLinearMap hf
  exact ⟨linEquiv, f.continuous,
    ContinuousLinearMap.continuous_symm_of_bijective f hf⟩

theorem ContinuousLinearMap.continuousLinearEquivOfBijective_apply
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) (v : V₁) :
    ContinuousLinearMap.continuousLinearEquivOfBijective f hf v = f v := by
  simp [ContinuousLinearMap.continuousLinearEquivOfBijective, LinearEquiv.ofBijective]

theorem ContinuousLinearMap.continuousLinearEquivOfBijective_coe
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    (ContinuousLinearMap.continuousLinearEquivOfBijective f hf : V₁ →L[ℂ] V₂) = f := by
  ext v
  exact ContinuousLinearMap.continuousLinearEquivOfBijective_apply f hf v













theorem clm_commuting_preserves_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (P : F →L[ℂ] F)
    (hcomm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I := by
  intro v hv

  show π.IsSmoothVector I (P v)
  have hv' : π.IsSmoothVector I v := hv
  unfold ContinuousRep.IsSmoothVector ContinuousRep.orbitMap at *


  have heq : (fun g : G => (π.toMonoidHom g) (P v)) =
             (fun g : G => P ((π.toMonoidHom g) v)) := by
    ext g; exact (hcomm g v).symm
  rw [heq]

  let P_real : F →L[ℝ] F := {
    toFun := P
    map_add' := P.map_add
    map_smul' := fun r w => by
      rw [show (r • w : F) = ((r : ℂ) • w : F) from by simp, map_smul]; simp
    cont := P.cont
  }
  exact P_real.contDiff.comp_contMDiff hv'

theorem schurProjector_commutes
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (_hirr : σ.IsIrreducible)
    (P : F →L[ℂ] F)
    (_hP_fix : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
    (_hP_range : ∀ v, P v ∈ π.IsotypicComponent K σ)
    (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v) :=
  hP_comm

theorem schurProjector_preserves_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible)
    (P : F →L[ℂ] F)
    (hP_fix : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
    (hP_range : ∀ v, P v ∈ π.IsotypicComponent K σ)
    (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I :=
  clm_commuting_preserves_smooth I π P
    (schurProjector_commutes π K σ hirr P hP_fix hP_range hP_comm)



















theorem invariant_subspace_map_subtype
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]

    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (U : Submodule ℂ ↥W)
    (hU_inv : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U) :
    (π.restrictSubgroup K).IsInvariantSubspace (Submodule.map W.subtype U) where


  isClosed := by
    rw [Submodule.map_coe]
    exact (hW_inv.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hU_inv.isClosed)


  invariant := by
    intro ⟨k, hk⟩ v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hv

    have hkw := hU_inv.invariant ⟨k, hk⟩ ⟨w, hw⟩ hwU

    refine ⟨((π.restrictSubgroup K).subrepresentation W hW_inv).toMonoidHom ⟨k, hk⟩ ⟨w, hw⟩, hkw, ?_⟩


    subst hwv

    rfl

theorem map_subtype_lt_of_ne_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (W : Submodule R M) (U : Submodule R ↥W) (hU : U ≠ ⊤) :
    Submodule.map W.subtype U < W := by
  refine lt_of_le_of_ne (Submodule.map_subtype_le W U) ?_
  intro h
  apply hU
  rw [eq_top_iff]
  intro ⟨v, hv⟩ _
  have hmem : v ∈ Submodule.map W.subtype U := by rw [h]; exact hv
  rw [Submodule.mem_map] at hmem
  obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hmem
  have : (⟨v, hv⟩ : ↥W) = ⟨w, hw⟩ := Subtype.ext (by simpa using hwv.symm)
  rw [this]; exact hwU










lemma isKFinite_of_orbit_le_finiteDim
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) (w : F)
    (W : Submodule ℂ F) [FiniteDimensional ℂ W]

    (hle : Submodule.span ℂ (Set.range (fun k : ↥K => π.toMonoidHom (↑k) w)) ≤ W) :
    ContinuousRep.IsKFinite π K w := by
  unfold ContinuousRep.IsKFinite
  exact Module.Finite.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end
