/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

namespace HomSheafCoherent

variable {R : Type*} [CommRing R]

/-- Over a Noetherian ring, `Hom_R(M, N)` is a finitely generated `R`-module whenever
both `M` and `N` are. -/
theorem hom_module_finite_of_noetherian [IsNoetherianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.Finite R (M →ₗ[R] N) := by

  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)

  let p : (Fin n → R) →ₗ[R] M := Finsupp.linearCombination R s ∘ₗ
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap

  have hp : Function.Surjective p := by
    rw [← LinearMap.range_eq_top]
    simp only [p, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Finsupp.range_linearCombination]
    exact hs

  let φ : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) := LinearMap.lcomp R N p
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    obtain ⟨y, rfl⟩ := hp x
    exact LinearMap.congr_fun h y

  haveI : IsNoetherian R ((Fin n → R) →ₗ[R] N) := inferInstance

  exact Module.Finite.of_injective φ hφ

/-- Localization commutes with `Hom` when `M` is finitely presented: the natural map
`S⁻¹ Hom(M, N) → Hom(S⁻¹ M, S⁻¹ N)` is a linear equivalence. -/
noncomputable def hom_localization_equiv
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[R]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N) :=
  Module.FinitePresentation.linearEquivMap S

/-- Noetherian version of `hom_localization_equiv`: over a Noetherian ring,
finitely generated implies finitely presented, so the Hom-localization equivalence holds. -/
noncomputable def hom_localization_equiv_noetherian [IsNoetherianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[R]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N) := by
  haveI : Module.FinitePresentation R M :=
    (Module.finitePresentation_iff_finite R M).mpr inferInstance
  exact Module.FinitePresentation.linearEquivMap S

/-- Combined statement: on an affine Noetherian scheme, the sheaf `Hom(F, G)` of two
coherent sheaves is again coherent — module-finiteness of Hom plus compatibility with
localization. -/
theorem sheafHom_coherent_on_affine [IsNoetherianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    Module.Finite R (M →ₗ[R] N) ∧
    ∀ (S : Submonoid R), Nonempty
      (LocalizedModule S (M →ₗ[R] N) ≃ₗ[R]
        (LocalizedModule S M →ₗ[R] LocalizedModule S N)) := by
  refine ⟨hom_module_finite_of_noetherian M N, fun S => ⟨?_⟩⟩
  exact hom_localization_equiv_noetherian M N S

end HomSheafCoherent
