/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.CompletePartialOrder

universe u

theorem lemma_23_58
    {R : Type u} [CommRing R]
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (φ : M →ₗ[R] N) (ψ : N →ₗ[R] P) :
    (Function.Exact φ ψ ∧ Function.Surjective ψ) ↔
    (∀ (D : Type u) [AddCommGroup D] [Module R D],
      Function.Injective (LinearMap.lcomp R D ψ) ∧
      Function.Exact (LinearMap.lcomp R D ψ) (LinearMap.lcomp R D φ)) := by
  constructor
  ·
    intro ⟨hex, hsurj⟩ D _ _
    refine ⟨LinearMap.lcomp_injective_of_surjective ψ hsurj, ?_⟩
    rw [LinearMap.exact_iff]
    ext g
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.lcomp_apply']
    constructor
    ·
      intro hg
      have hker : ψ.ker ≤ g.ker := by
        rw [hex.linearMap_ker_eq]
        intro x hx
        obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
        exact LinearMap.ext_iff.mp hg y
      exact ⟨(ψ.ker.liftQ g hker) ∘ₗ (ψ.quotKerEquivOfSurjective hsurj).symm.toLinearMap,
        by ext n; simp [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]⟩
    ·
      intro ⟨f, hf⟩
      rw [← hf]; ext x
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
        hex.apply_apply_eq_zero]
  ·
    intro h
    have get_inj : ∀ (D : Type u) [AddCommGroup D] [Module R D],
        Function.Injective (LinearMap.lcomp R D ψ) := fun D _ _ => (h D).1
    have get_exact : ∀ (D : Type u) [AddCommGroup D] [Module R D],
        Function.Exact (LinearMap.lcomp R D ψ) (LinearMap.lcomp R D φ) := fun D _ _ => (h D).2
    constructor
    ·
      rw [LinearMap.exact_iff]
      apply le_antisymm
      ·
        intro n hn
        simp only [LinearMap.mem_ker] at hn
        have hexD := get_exact (N ⧸ φ.range)
        rw [LinearMap.exact_iff] at hexD
        have hπ_ker : φ.range.mkQ ∈ (LinearMap.lcomp R (N ⧸ φ.range) φ).ker := by
          simp only [LinearMap.mem_ker, LinearMap.lcomp_apply']
          ext m
          simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
            Submodule.Quotient.mk_eq_zero]
          exact LinearMap.mem_range.mpr ⟨m, rfl⟩
        rw [hexD] at hπ_ker
        obtain ⟨σ, hσ⟩ := LinearMap.mem_range.mp hπ_ker
        simp only [LinearMap.lcomp_apply'] at hσ

        have : φ.range.mkQ n = 0 := by
          rw [← hσ]; simp only [LinearMap.comp_apply, hn, map_zero]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        exact this

      ·
        rw [LinearMap.range_le_ker_iff]
        have hcomp := (get_exact P).linearMap_comp_eq_zero
        ext x
        have := LinearMap.ext_iff.mp hcomp (LinearMap.id)
        simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.lcomp_apply'] at this
        simp only [LinearMap.comp_apply, LinearMap.zero_apply]
        exact LinearMap.ext_iff.mp this x
    ·
      rw [← LinearMap.range_eq_top]
      have hinj' := get_inj (P ⧸ ψ.range)
      have hmkq_zero : (LinearMap.lcomp R (P ⧸ ψ.range) ψ) ψ.range.mkQ = 0 := by
        ext n
        simp only [LinearMap.lcomp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact LinearMap.mem_range.mpr ⟨n, rfl⟩
      have h0 : ψ.range.mkQ = 0 := hinj'
        (show (LinearMap.lcomp R _ ψ) ψ.range.mkQ = (LinearMap.lcomp R _ ψ) 0 by
          rw [hmkq_zero, map_zero])
      ext x
      simp only [Submodule.mem_top, iff_true]
      have := LinearMap.ext_iff.mp h0 x
      simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
