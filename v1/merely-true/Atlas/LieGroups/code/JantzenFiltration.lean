/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Atlas.LieGroups.code.HarishChandraIsomorphism

noncomputable section

universe u_mod u_ch

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure JantzenFiltrationData
    (V₀ : Type*) [AddCommGroup V₀] [Module R V₀] where
  level : ℕ → Submodule R V₀
  level_zero : level 0 = ⊤
  antitone : Antitone level
  iInf_eq_bot : ⨅ m, level m = ⊥

structure VermaJantzenFiltration
    {Δ : TriangularDecomposition R 𝔤}
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVM : IsVermaModule Δ M wt) where
  level : ℕ → LieSubmodule R 𝔤 M
  level_zero : level 0 = ⊤
  antitone : Antitone level
  iInf_eq_bot : ⨅ i, level i = ⊥
  level_one_is_maximal : level 1 ≠ ⊤ ∧
    (∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ level 1)

end

section JantzenFiltrationProps

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}

theorem VermaJantzenFiltration.level_one_ne_top
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    {hVM : IsVermaModule Δ M wt}
    (filt : VermaJantzenFiltration R 𝔤 M wt hVM) :
    filt.level 1 ≠ ⊤ :=
  filt.level_one_is_maximal.1

theorem VermaJantzenFiltration.level_one_max
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    {hVM : IsVermaModule Δ M wt}
    (filt : VermaJantzenFiltration R 𝔤 M wt hVM)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤) :
    N ≤ filt.level 1 :=
  filt.level_one_is_maximal.2 N hN

end JantzenFiltrationProps

noncomputable section JantzenSumFormula

open Classical

universe u_mod' u_ch'

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}

structure RootCorootData (rd : PositiveRootData Δ) where
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R

def RootCorootData.ofPositiveRootData (rd : PositiveRootData Δ) : RootCorootData rd :=
  ⟨rd.corootPairing⟩

def dotReflectedWeight {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    (cd : RootCorootData rd)
    (lam : Δ.𝔥 →ₗ[R] R) (α : Δ.𝔥 →ₗ[R] R) :
    Δ.𝔥 →ₗ[R] R :=
  lam - cd.corootPairing (lam + wg.ρ) α • α

structure FormalCharacterData
    (M : Type u_mod') [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVM : IsVermaModule Δ M wt) where
  CharGroup : Type u_ch'
  [instACG : AddCommGroup CharGroup]
  chSub : LieSubmodule R 𝔤 M → CharGroup
  chVerma : (Δ.𝔥 →ₗ[R] R) → CharGroup
  ch_top : chSub ⊤ = chVerma wt
  ch_bot : chSub ⊥ = 0

attribute [instance] FormalCharacterData.instACG

def jantzenSumRoots {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    (cd : RootCorootData rd)
    (lam : Δ.𝔥 →ₗ[R] R) : Finset (Δ.𝔥 →ₗ[R] R) :=
  rd.posRoots.filter (fun α =>
    ∃ n : ℕ, 0 < n ∧ cd.corootPairing (lam + wg.ρ) α = (n : R))

end JantzenSumFormula
