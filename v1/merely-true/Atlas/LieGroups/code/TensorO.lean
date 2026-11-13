/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Multiset.Basic

universe v

noncomputable section

lemma IsCategoryO_of_lieEquiv
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {A : Type*} [AddCommGroup A] [Module R A]
    [LieRingModule 𝔤 A] [LieModule R 𝔤 A]
    {B : Type*} [AddCommGroup B] [Module R B]
    [LieRingModule 𝔤 B] [LieModule R 𝔤 B]
    (f : A ≃ₗ⁅R, 𝔤⁆ B)
    (hB : IsCategoryO Δ rd B) :
    IsCategoryO Δ rd A where
  finitely_generated := by
    obtain ⟨S, hS⟩ := hB.finitely_generated
    set T := S.map ⟨f.symm, f.symm.injective⟩ with hT_def
    refine ⟨T, ?_⟩
    set N := LieSubmodule.lieSpan R 𝔤 (↑T : Set A) with hN_def
    set fN := LieSubmodule.map f.toLieModuleHom N with hfN_def
    have hS_sub_fN : (↑S : Set B) ⊆ (fN : Set B) := by
      intro s hs
      show s ∈ fN
      rw [hfN_def, LieSubmodule.mem_map]
      exact ⟨f.symm s, LieSubmodule.subset_lieSpan (by
        rw [hT_def, Finset.coe_map]; exact ⟨s, hs, rfl⟩),
        f.apply_symm_apply s⟩
    have hfN_eq_top : fN = ⊤ := by
      rw [eq_top_iff, ← hS]
      exact LieSubmodule.lieSpan_le.mpr hS_sub_fN
    rw [eq_top_iff]
    intro a _
    have hfa_in : f a ∈ fN := hfN_eq_top ▸ LieSubmodule.mem_top _
    rw [hfN_def, LieSubmodule.mem_map] at hfa_in
    obtain ⟨a', ha', hfa'⟩ := hfa_in
    have heq : a' = a := f.injective hfa'
    rwa [← heq]
  weight_decomp := by
    intro a
    obtain ⟨S, v, hv⟩ := hB.weight_decomp (f a)
    refine ⟨S, fun μ => ⟨f.symm (v μ : B), fun h => ?_⟩, ?_⟩
    · have hvm := (v μ).prop h
      apply f.injective
      rw [show f ⁅(↑h : 𝔤), f.symm ↑(v μ)⁆ =
        ⁅(↑h : 𝔤), f (f.symm ↑(v μ))⁆ from by
          show (f : A →ₗ⁅R,𝔤⁆ B) ⁅(↑h : 𝔤), f.symm ↑(v μ)⁆ =
            ⁅(↑h : 𝔤), (f : A →ₗ⁅R,𝔤⁆ B) (f.symm ↑(v μ))⁆
          rw [LieModuleHom.map_lie]]
      rw [f.apply_symm_apply, hvm, map_smul, f.apply_symm_apply]
    · apply f.injective
      rw [map_sum]
      simp only [f.apply_symm_apply]
      exact hv
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hB.weight_bound
    refine ⟨bds, fun μ hμ => ?_⟩
    have hμB : μ ∈ weights Δ B := by
      rw [weights, Set.mem_setOf_eq] at hμ ⊢
      intro hbot
      apply hμ
      rw [eq_bot_iff]
      intro a ha
      have hfa : f a ∈ WeightSpace Δ B μ := by
        intro hh
        show ⁅(↑hh : 𝔤), (f : A →ₗ⁅R,𝔤⁆ B) a⁆ = μ hh • (f : A →ₗ⁅R,𝔤⁆ B) a
        rw [← LieModuleHom.map_lie, ha hh, map_smul]
      rw [hbot] at hfa
      simp [Submodule.mem_bot] at hfa
      exact hfa
    exact hbds μ hμB



structure HasVermaFiltration
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (Δ_weights : Multiset (Δ.𝔥 →ₗ[R] R)) where
  length : ℕ
  filtration : Fin (length + 1) → LieSubmodule R 𝔤 M
  mono : ∀ i : Fin length, filtration ⟨i, by omega⟩ ≤ filtration ⟨i + 1, by omega⟩
  bot : filtration ⟨0, by omega⟩ = ⊥
  top : filtration ⟨length, Nat.lt_succ_iff.mpr (le_refl _)⟩ = ⊤
  quotient_weights : Fin length → (Δ.𝔥 →ₗ[R] R)
  weights_eq : (Finset.univ.val.map quotient_weights) = Δ_weights
  quotient_is_verma : ∀ i : Fin length,
    ∃ (Q : Type*) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q),
      Nonempty (IsVermaModule Δ Q (quotient_weights i))




structure CategoryOProperties
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  noetherian : ∀ (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    ∀ (chain : ℕ → LieSubmodule R 𝔤 M),
      (∀ n, chain n ≤ chain (n + 1)) →
      ∃ N, ∀ n, N ≤ n → chain n = chain N
  enough_projectives : ∀ (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    ∃ (P : Type*) (_ : AddCommGroup P) (_ : Module R P)
      (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P)
      (hPO : IsCategoryO Δ rd P),
      IsProjectiveInO rd P hPO ∧
      ∃ (f : P →ₗ⁅R, 𝔤⁆ M), Function.Surjective f
  hom_finiteDimensional : ∀ (P : Type*) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P],
    ∀ (hPO : IsCategoryO Δ rd P),
    IsProjectiveInO rd P hPO →
    ∀ (M : Type*) [AddCommGroup M] [Module R M]
      [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    Module.Finite R (P →ₗ⁅R, 𝔤⁆ M)

end
