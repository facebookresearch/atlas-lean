/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module

open Submodule LinearMap

noncomputable section

section BilinPairingProperties

variable (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

def BilinPairing.IsSymmetric (B : M →ₗ[A] M →ₗ[A] A) : Prop :=
  LinearMap.BilinForm.IsSymm B

def BilinPairing.inducedMap (B : M →ₗ[A] M →ₗ[A] A) : M →ₗ[A] Module.Dual A M :=
  B

end BilinPairingProperties

abbrev IsPerfectSelfPairing (A : Type*) [CommRing A] (M : Type*)
    [AddCommGroup M] [Module A M] (p : M →ₗ[A] M →ₗ[A] A) : Prop :=
  p.IsPerfPair

structure IsALattice
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (M : Submodule A V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span K (M : Set V) = ⊤

section DualLattice

variable
  (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

def dualLattice (φ : V →ₗ[K] V →ₗ[K] K) (M : Submodule A V) : Submodule A V where
  carrier := {v : V | ∀ m ∈ M, φ v m ∈ (algebraMap A K).range}
  add_mem' {a b} (ha : ∀ m ∈ M, φ a m ∈ _) (hb : ∀ m ∈ M, φ b m ∈ _) m hm := by
    rw [map_add, add_apply]
    exact Subring.add_mem _ (ha m hm) (hb m hm)
  zero_mem' m _ := by
    rw [map_zero, zero_apply]
    exact Subring.zero_mem _
  smul_mem' c v (hv : ∀ m ∈ M, φ v m ∈ _) m hm := by
    have h1 : c • v = (algebraMap A K c) • v := by
      rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [h1, map_smul, smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv m hm)

end DualLattice
