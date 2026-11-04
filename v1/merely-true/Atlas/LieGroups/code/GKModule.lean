/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ContinuousRep
import Atlas.LieGroups.code.KFinite
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

def Representation.IsLocallyFinite {K V : Type*} [Group K]
    [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ K V) : Prop :=
  ∀ v : V, FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun k : K => (σ k) v)) : Submodule ℂ V)

structure GKModule
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V] where
  σ : Representation ℂ K V
  locallyFinite : σ.IsLocallyFinite
  diffσ : 𝔨 →ₗ[ℂ] (V →ₗ[ℂ] V)
  diff_eq_lie : ∀ (X : 𝔨) (v : V), diffσ X v = ⁅(X : 𝔤), v⁆
  equivariance : ∀ (k : K) (X : 𝔤) (v : V),
    σ k (⁅X, v⁆) = ⁅Ad k X, σ k v⁆

structure GKModuleHom
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) where
  toLinearMap : V →ₗ[ℂ] W
  lie_comm : ∀ (X : 𝔤) (v : V), toLinearMap ⁅X, v⁆ = ⁅X, toLinearMap v⁆
  group_comm : ∀ (k : K) (v : V), toLinearMap (M.σ k v) = N.σ k (toLinearMap v)

namespace GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

structure IsSubmodule (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop where
  lie_invariant : ∀ (X : 𝔤) (w : V), w ∈ W → ⁅X, w⁆ ∈ W
  group_invariant : ∀ (k : K) (w : V), w ∈ W → M.σ k w ∈ W

def IsIrreducibleGKModule (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∀ (W : Submodule ℂ V), M.IsSubmodule W → W = ⊥ ∨ W = ⊤

def IsKInvariant (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop :=
  ∀ (k : K) (v : V), v ∈ W → M.σ k v ∈ W

def IsKIrreducible (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop :=
  M.IsKInvariant W ∧
  ∀ (U : Submodule ℂ V), U ≤ W → M.IsKInvariant U → U = ⊥ ∨ U = W

def AreKIsomorphic (M : GKModule 𝔤 K 𝔨 Ad V)
    (W₁ W₂ : Submodule ℂ V)
    (h₁ : M.IsKInvariant W₁) (h₂ : M.IsKInvariant W₂) : Prop :=
  ∃ (f : W₁ ≃ₗ[ℂ] W₂), ∀ (k : K) (v : W₁),
    f ⟨M.σ k ↑v, h₁ k ↑v v.2⟩ = ⟨M.σ k ↑(f v), h₂ k ↑(f v) (f v).2⟩

def KIsotypicComponent (M : GKModule 𝔤 K 𝔨 Ad V)
    (W₀ : Submodule ℂ V) (hW₀ : M.IsKIrreducible W₀) : Submodule ℂ V :=
  sSup { W : Submodule ℂ V |
    ∃ (hIrr : M.IsKIrreducible W),
      M.AreKIsomorphic W W₀ hIrr.1 hW₀.1 }

def IsAdmissible (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∀ (W₀ : Submodule ℂ V) (hW₀ : M.IsKIrreducible W₀),
    FiniteDimensional ℂ (M.KIsotypicComponent W₀ hW₀)

end GKModule

end
