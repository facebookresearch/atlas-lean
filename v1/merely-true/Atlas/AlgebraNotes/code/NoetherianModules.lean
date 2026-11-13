/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace NoetherianModules

theorem noetherian_iff_fg_modules_noetherian (R : Type u) [CommRing R] :
    IsNoetherianRing R ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], IsNoetherian R M := by
  constructor
  · intro h M _ _ _
    exact isNoetherian_of_isNoetherianRing_of_finite R M
  · intro h
    have : IsNoetherian R R := h R
    exact isNoetherianRing_iff.mpr this

theorem finitePresentation_iff (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
      ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f ∧ (LinearMap.ker f).FG := by
  constructor
  · intro h
    haveI : Module.Finite R M := inferInstance
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let e := (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm
    let φ := (Finsupp.linearCombination R s).comp e.toLinearMap
    have hφ_surj : Function.Surjective φ := by
      intro m
      have hm : m ∈ Submodule.span R (Set.range s) := by rw [hs]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨c, ?_⟩
      simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [show e c = Finsupp.equivFunOnFinite.symm c from rfl]
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype]
      · simp [Finsupp.equivFunOnFinite, hc]
      · intro i; simp
    have hφ_ker : (LinearMap.ker φ).FG :=
      Module.FinitePresentation.fg_ker φ hφ_surj
    exact ⟨n, φ, hφ_surj, hφ_ker⟩
  · intro ⟨n, f, hf_surj, hf_ker⟩
    exact Module.finitePresentation_of_surjective f hf_surj hf_ker

theorem fg_module_finitely_presented (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] : Module.FinitePresentation R M :=
  Module.finitePresentation_of_finite R M

theorem noetherian_ring_iff_acc (R : Type*) [CommRing R] :
    IsNoetherianRing R ↔ ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m := by
  rw [isNoetherianRing_iff]
  exact monotone_stabilizes_iff_noetherian.symm

theorem surjective_hom_fg
    {R : Type*} {M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (Module.Finite R M → Module.Finite R N) ∧
    (Module.Finite R N → (LinearMap.ker f).FG → Module.Finite R M) := by
  constructor
  · intro hM
    exact Module.Finite.of_surjective f hf
  · intro hN hker
    rw [Module.finite_def]
    have h1 : (Submodule.map f ⊤).FG := by
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr hf]
      exact hN.fg_top
    have h2 : (⊤ ⊓ LinearMap.ker f).FG := by
      rw [top_inf_eq]
      exact hker
    exact Submodule.fg_of_fg_map_of_fg_inf_ker f h1 h2
