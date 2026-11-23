/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible

noncomputable section

structure SmoothVarietyWithGroupAction where
  X : Type*
  K : Type*
  [grpK : Group K]
  [topK : TopologicalSpace K]
  [connK : ConnectedSpace K]
  [actKX : MulAction K X]
  DX : Type*
  [ringDX : Ring DX]
  [algebraDX : Algebra ℂ DX]
  [actKDX : MulAction K DX]
  orbits : Set (Set X)
  orbit_is_orbit : ∀ O ∈ orbits, O.Nonempty ∧ (∀ x ∈ O, ∀ k : K, k • x ∈ O)
  orbits_cover : ∀ x : X, ∃ O ∈ orbits, x ∈ O
  orbits_disjoint : ∀ O₁ ∈ orbits, ∀ O₂ ∈ orbits, O₁ ≠ O₂ → Disjoint O₁ O₂
  orbits_finite : orbits.Finite

attribute [instance] SmoothVarietyWithGroupAction.grpK
attribute [instance] SmoothVarietyWithGroupAction.topK
attribute [instance] SmoothVarietyWithGroupAction.connK
attribute [instance] SmoothVarietyWithGroupAction.actKX
attribute [instance] SmoothVarietyWithGroupAction.ringDX
attribute [instance] SmoothVarietyWithGroupAction.algebraDX
attribute [instance] SmoothVarietyWithGroupAction.actKDX

def SmoothVarietyWithGroupAction.stabilizer (S : SmoothVarietyWithGroupAction)
    (x : S.X) : Subgroup S.K :=
  MulAction.stabilizer S.K x

structure OrbitRepPair (S : SmoothVarietyWithGroupAction) where
  orbit : Set S.X
  orbit_mem : orbit ∈ S.orbits
  basepoint : S.X
  basepoint_mem : basepoint ∈ orbit
  ComponentGroup : Type*
  [compGrpGroup : Group ComponentGroup]
  quotientMap : (MulAction.stabilizer S.K basepoint) →* ComponentGroup
  quotientMap_surjective : Function.Surjective quotientMap
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  compGroupRep : Representation ℂ ComponentGroup V
  V_irreducible : compGroupRep.IsIrreducible

attribute [instance] OrbitRepPair.addCommGroupV
attribute [instance] OrbitRepPair.moduleV
attribute [instance] OrbitRepPair.compGrpGroup

structure IrredKEquivDModule (S : SmoothVarietyWithGroupAction) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [moduleC : Module ℂ carrier]
  [moduleDX : Module S.DX carrier]
  [mulActionK : MulAction S.K carrier]
  equivariance : ∀ (k : S.K) (d : S.DX) (m : carrier),
    k • (d • m) = (k • d) • (k • m)
  isIrreducible : IsSimpleModule S.DX carrier

attribute [instance] IrredKEquivDModule.addCommGroup
attribute [instance] IrredKEquivDModule.moduleC
attribute [instance] IrredKEquivDModule.moduleDX
attribute [instance] IrredKEquivDModule.mulActionK

def IrredKEquivDModule.IsIsomorphic (S : SmoothVarietyWithGroupAction)
    (M N : IrredKEquivDModule S) : Prop :=
  Nonempty (M.carrier ≃ₗ[S.DX] N.carrier)









structure HarishChandraData where
  G : Type*
  [grpG : Group G]
  K : Type*
  [grpK : Group K]
  𝔤 : Type*
  [lieRing𝔤 : LieRing 𝔤]
  [lieAlgebra𝔤 : LieAlgebra ℂ 𝔤]
  𝓕 : Type*
  [actK𝓕 : MulAction K 𝓕]
  W : Type*
  [grpW : Group W]
  [fintypeW : Fintype W]
  Z_Ug : Type*
  [commRingZ : CommRing Z_Ug]
  [algebraZ : Algebra ℂ Z_Ug]
  [dotActionW : MulAction W (Z_Ug →ₐ[ℂ] ℂ)]
  antidominance_pred : (Z_Ug →ₐ[ℂ] ℂ) → Prop

attribute [instance] HarishChandraData.grpG
attribute [instance] HarishChandraData.grpK
attribute [instance] HarishChandraData.lieRing𝔤
attribute [instance] HarishChandraData.lieAlgebra𝔤
attribute [instance] HarishChandraData.actK𝓕
attribute [instance] HarishChandraData.grpW
attribute [instance] HarishChandraData.fintypeW
attribute [instance] HarishChandraData.commRingZ
attribute [instance] HarishChandraData.algebraZ
attribute [instance] HarishChandraData.dotActionW

def HarishChandraData.IsRegularChar (D : HarishChandraData) (χ : D.Z_Ug →ₐ[ℂ] ℂ) : Prop :=
  ∀ w : D.W, w • χ = χ → w = 1

class HarishChandraData.IsAntidominantChar (D : HarishChandraData)
    (χ : D.Z_Ug →ₐ[ℂ] ℂ) : Prop where
  antidominant_rep_exists : D.antidominance_pred χ


structure HCGKModule (D : HarishChandraData) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  [lieRingModule : LieRingModule D.𝔤 carrier]
  [lieModule : LieModule ℂ D.𝔤 carrier]
  [mulAction : MulAction D.K carrier]
  χ : D.Z_Ug →ₐ[ℂ] ℂ

attribute [instance] HCGKModule.addCommGroup
attribute [instance] HCGKModule.module
attribute [instance] HCGKModule.lieRingModule
attribute [instance] HCGKModule.lieModule
attribute [instance] HCGKModule.mulAction

def HCGKModule.IsGKSubmodule {D : HarishChandraData} (M : HCGKModule D)
    (W : Submodule ℂ M.carrier) : Prop :=
  (∀ (X : D.𝔤) (m : M.carrier), m ∈ W → ⁅X, m⁆ ∈ W) ∧
  (∀ (k : D.K) (m : M.carrier), m ∈ W → k • m ∈ W)

def HCGKModule.IsIrreducible {D : HarishChandraData} (M : HCGKModule D) : Prop :=
  Nontrivial M.carrier ∧
  ∀ W : Submodule ℂ M.carrier, M.IsGKSubmodule W → W = ⊥ ∨ W = ⊤

structure HCClassifyingDatum (D : HarishChandraData) where
  basepoint : D.𝓕
  orbit : Set D.𝓕
  orbit_eq : orbit = MulAction.orbit D.K basepoint
  K_x : Subgroup D.K
  K_x_eq : K_x = MulAction.stabilizer D.K basepoint
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  stabRep : Representation ℂ K_x V
  V_irreducible : stabRep.IsIrreducible
  lieKx : LieSubalgebra ℂ D.𝔤
  char_lieKx : D.𝔤 →ₗ[ℂ] ℂ
  lieKx_action : lieKx →ₗ[ℂ] (V →ₗ[ℂ] V)
  char_lieKx_acts : ∀ (X : lieKx) (v : V), lieKx_action X v = char_lieKx (X : D.𝔤) • v

attribute [instance] HCClassifyingDatum.addCommGroupV
attribute [instance] HCClassifyingDatum.moduleV





end
