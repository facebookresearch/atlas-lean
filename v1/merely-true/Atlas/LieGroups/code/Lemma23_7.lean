/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ProjectiveFunctors
import Atlas.LieGroups.code.HeckeKL

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

def IsInXi0_23_7
    (rd : PositiveRootData Δ) (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def WeylStabilizer_23_7
    (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w | wg.dualAction w lam = lam}

def BruhatLE_23_7
    (rd : PositiveRootData Δ) (mu nu : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ),
    nu - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsDominant_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), BruhatLE_23_7 rd (wg.dualAction w lam) lam

structure IsProperRep_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop where
  lam_dominant : IsDominant_23_7 rd wg lam
  in_xi0 : IsInXi0_23_7 rd mu lam
  mu_minimal : ∀ (w : wg.W), w ∈ WeylStabilizer_23_7 wg lam →
    BruhatLE_23_7 rd mu (wg.dualAction w mu)

def WeylOrbitPair_23_7
    (wg : WeylGroupData Δ) (mu lam : Δ.𝔥 →ₗ[R] R) :
    Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | ∃ w : wg.W, p = (wg.dualAction w mu, wg.dualAction w lam)}

structure BilinFormData_23_7
    (wg : WeylGroupData Δ) [LE R] where
  normSq : (Δ.𝔥 →ₗ[R] R) → R
  weyl_invariant : ∀ (w : wg.W) (v : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w v) = normSq v
  normSq_sub_weyl_invariant : ∀ (w : wg.W) (a b : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w a - wg.dualAction w b) = normSq (a - b)

structure SupportData_23_7
    (wg : WeylGroupData Δ) where
  support : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
  weyl_equivariant : ∀ (w : wg.W) (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)),
    p ∈ support → (wg.dualAction w p.1, wg.dualAction w p.2) ∈ support

def maximalSupport_23_7 [LE R]
    {wg : WeylGroupData Δ} (B : BilinFormData_23_7 wg) (S : SupportData_23_7 wg) :
    Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | p ∈ S.support ∧
    ∀ q ∈ S.support, B.normSq (q.2 - q.1) ≤ B.normSq (p.2 - p.1)}








end
