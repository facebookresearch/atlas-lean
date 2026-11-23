/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Mathlib.Algebra.Lie.Sl2

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def IsSingularVector
    (Δ : TriangularDecomposition R 𝔤)
    {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (v : M) : Prop :=
  (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) ∧
  (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0)

structure ChevalleyData (Δ : TriangularDecomposition R 𝔤) where
  rank : ℕ
  simpleCoroot : Fin rank → Δ.𝔥
  posGen : Fin rank → 𝔤
  negGen : Fin rank → 𝔤
  posGen_mem : ∀ i, posGen i ∈ Δ.𝔫_pos
  negGen_mem : ∀ i, negGen i ∈ Δ.𝔫_neg
  bracket_ef : ∀ i, ⁅posGen i, negGen i⁆ = (simpleCoroot i : 𝔤)
  bracket_he : ∀ i, ⁅(simpleCoroot i : 𝔤), posGen i⁆ = posGen i + posGen i
  bracket_hf : ∀ i, ⁅(simpleCoroot i : 𝔤), negGen i⁆ = -(negGen i + negGen i)

theorem ChevalleyData.sl2_weight_integrality
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ)
    (i : Fin chev.rank)
    {V : Type u_mod} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [IsNoetherian R V] [Module.IsTorsionFree R V] [IsDomain R] [CharZero R]
    (v : V) (hv : v ≠ 0)
    (he : ⁅chev.posGen i, v⁆ = 0)
    (μ : R) (hh : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = μ • v) :
    ∃ (n : ℕ), μ = (n : R) := by


  by_cases hhz : (chev.simpleCoroot i : 𝔤) = 0
  ·
    have hμv : μ • v = 0 := by rw [← hh, hhz, zero_lie]
    have hμ0 : μ = 0 := by
      by_contra hμ
      have hreg : IsRegular μ :=
        ⟨fun a b hab => mul_left_cancel₀ hμ hab,
         fun a b hab => mul_right_cancel₀ hμ hab⟩
      have hsmul : IsSMulRegular V μ :=
        Module.IsTorsionFree.isSMulRegular (M := V) hreg
      exact hv (hsmul (show μ • v = μ • 0 by simp [hμv]))
    exact ⟨0, by simp [hμ0]⟩
  ·
    have t : IsSl2Triple (chev.simpleCoroot i : 𝔤) (chev.posGen i) (chev.negGen i) :=
      IsSl2Triple.mk hhz
        (chev.bracket_ef i)
        (by rw [two_nsmul]; exact chev.bracket_he i)
        (by rw [two_nsmul]; exact chev.bracket_hf i)
    have P : t.HasPrimitiveVectorWith v μ :=
      IsSl2Triple.HasPrimitiveVectorWith.mk hv hh he
    exact P.exists_nat

def ChevalleyData.IsDominantIntegral
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ) (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (i : Fin chev.rank), ∃ (n : ℕ), wt (chev.simpleCoroot i) = (n : R)

def ChevalleyData.IsInWeightLattice
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ) (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (i : Fin chev.rank), ∃ (n : ℤ), wt (chev.simpleCoroot i) = (n : R)

theorem exercise_8_11
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ)
    (wt : Δ.𝔥 →ₗ[R] R)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [IsNoetherian R V] [Module.IsTorsionFree R V] [IsDomain R] [CharZero R]
    (hV : IsHighestWeightModule Δ V wt)
    (i : Fin chev.rank) :
    ∃ (n : ℕ), wt (chev.simpleCoroot i) = (n : R) := by


  set v := hV.highestWeightVec with hv_def
  set μ := wt (chev.simpleCoroot i) with hμ_def

  have he_v : ⁅chev.posGen i, v⁆ = 0 :=
    hV.npos_action ⟨chev.posGen i, chev.posGen_mem i⟩

  have hh_v : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = μ • v :=
    hV.cartan_action (chev.simpleCoroot i)

  exact chev.sl2_weight_integrality i v hV.hwv_ne_zero he_v μ hh_v




end
