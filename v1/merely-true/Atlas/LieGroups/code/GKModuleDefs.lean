/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.Admissible
import Mathlib.Algebra.Lie.Semisimple.Defs

noncomputable section

open scoped ComplexOrder

structure HarishChandraPair
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K] where
  𝔨 : LieSubalgebra ℂ 𝔤
  Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)

namespace GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def lieIterate (Xs : List 𝔤) (v : V) : V :=
  Xs.foldr (fun X acc => ⁅X, acc⁆) v

def IsHarishChandraModule (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  M.IsAdmissible ∧
  ∃ (S : Finset V), ∀ v : V,
    v ∈ Submodule.span ℂ
      (⋃ (s : V) (_ : s ∈ S) (Xs : List 𝔤),
        ({lieIterate Xs s} : Set V))

end GKModule

structure SemisimpleLieGroup where
  G : Type*
  instGroup : Group G
  instTopologicalSpace : TopologicalSpace G
  instIsTopologicalGroup : IsTopologicalGroup G
  𝔤 : Type*
  instLieRing : LieRing 𝔤
  instLieAlgebra : LieAlgebra ℝ 𝔤
  isSemisimple : LieAlgebra.IsSemisimple ℝ 𝔤
  lieExp : 𝔤 → G
  lieExp_zero : lieExp 0 = @One.one G instGroup.toOne


instance (SG : SemisimpleLieGroup) : Group SG.G := SG.instGroup
instance (SG : SemisimpleLieGroup) : TopologicalSpace SG.G := SG.instTopologicalSpace
instance (SG : SemisimpleLieGroup) : IsTopologicalGroup SG.G := SG.instIsTopologicalGroup

instance (SG : SemisimpleLieGroup) : LieRing SG.𝔤 := SG.instLieRing
instance (SG : SemisimpleLieGroup) : LieAlgebra ℝ SG.𝔤 := SG.instLieAlgebra

def IsMaximalCompactSubgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    (K : Subgroup G) [TopologicalSpace K]
    [CompactSpace K] : Prop :=
  ∀ (H : Subgroup G) [TopologicalSpace H] [CompactSpace H],
    ∃ (g : G), ∀ h : G, h ∈ H → g * h * g⁻¹ ∈ K



def GKModule.IsFiniteLength
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∃ n : ℕ, ∃ (chain : Fin (n + 1) → Submodule ℂ V),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧
    (∀ i : Fin n,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
        chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
    (∀ i : Fin n,
      M.IsSubmodule (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) ∧
    (∀ i : Fin n,
      M.IsSubmodule (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧


    (∀ i : Fin n, ∀ (W : Submodule ℂ V), M.IsSubmodule W →
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ W →
      W ≤ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ →
      W = chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ∨
      W = chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

end
