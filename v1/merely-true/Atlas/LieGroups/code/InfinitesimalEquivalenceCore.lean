/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.HarishChandraFunctor
import Atlas.LieGroups.code.Admissible
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

structure GKModuleIso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) where
  toLinearEquiv : V ≃ₗ[ℂ] W
  lie_comm : ∀ (X : 𝔤) (v : V), toLinearEquiv ⁅X, v⁆ = ⁅X, toLinearEquiv v⁆
  group_comm : ∀ (k : K) (v : V), toLinearEquiv (M.σ k v) = N.σ k (toLinearEquiv v)

def InfinitesimallyEquivalent
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂) : Prop :=
  Nonempty (GKModuleIso M₁ M₂)

structure GKModule.IsUnitary
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w)
  re_nonneg : ∀ (v : V), 0 ≤ (form v v).re
  definite : ∀ (v : V), form v v = 0 → v = 0
  pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re
  K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w
  lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0

def GKModule.IsUnitary.mk'
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w))
    (pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re)
    (K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w)
    (lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0) :
    M.IsUnitary where
  form := form
  conj_symm := conj_symm
  re_nonneg := fun v => by
    by_cases hv : v = 0
    · subst hv; simp [map_zero, LinearMap.map_zero]
    · exact le_of_lt (pos_def v hv)
  definite := fun v hfv => by
    by_contra hv
    have h := pos_def v hv
    rw [hfv, Complex.zero_re] at h
    exact lt_irrefl 0 h
  pos_def := pos_def
  K_invariant := K_invariant
  lie_invariant := lie_invariant

noncomputable def GKModule.IsUnitary.toInnerProductSpaceCore
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (hu : M.IsUnitary) : InnerProductSpace.Core ℂ V where
  inner v w := hu.form v w
  conj_inner_symm x y := (hu.conj_symm y x).symm
  re_inner_nonneg x := hu.re_nonneg x
  add_left x y z := by simp [map_add, LinearMap.add_apply]
  smul_left x y r := by simp [LinearMapClass.map_smul]
  definite x hx := hu.definite x (by exact_mod_cast hx)

structure Globalization
    (G : Type*) [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    (K_sub : K →* G)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  Ŵ : Type*
  instNACG : NormedAddCommGroup Ŵ
  instIPS : @InnerProductSpace ℂ Ŵ _ instNACG.toSeminormedAddCommGroup
  instCS : @CompleteSpace Ŵ instNACG.toUniformSpace
  π : @ContinuousRep G _ _ Ŵ instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
  isUnitary : @ContinuousRep.IsUnitary G _ _ Ŵ instNACG instIPS instCS π
  isIrreducible : @ContinuousRep.IsIrreducible G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace π
  ι : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) V Ŵ
      _ instNACG.toAddCommGroup.toAddCommMonoid _ instIPS.toNormedSpace.toModule
  ι_injective : Function.Injective ι
  K_compat : ∀ (k : K) (v : V), ι (M.σ k v) = (π.toMonoidHom (K_sub k)) (ι v)
  lie_action_Ŵ : 𝔤 → Ŵ → Ŵ
  lie_compat_ι : ∀ (X : 𝔤) (v : V), ι ⁅X, v⁆ = lie_action_Ŵ X (ι v)
  kfin_image : Set.range ι =
    ↑(@ContinuousRep.kFiniteSubspace G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
      π K_sub.range)

attribute [instance] Globalization.instNACG Globalization.instIPS Globalization.instCS
















end
