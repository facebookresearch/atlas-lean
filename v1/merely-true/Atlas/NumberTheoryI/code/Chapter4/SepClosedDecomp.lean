/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Polynomial TensorProduct Module

noncomputable section

namespace SepClosedDecomposition

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsSepClosed Ω]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

theorem algHom_card_eq_finrank_of_isSepClosed :
    Fintype.card (L →ₐ[K] Ω) = finrank K L :=
  AlgHom.card_of_splits K L Ω
    (fun x => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x))

def evalAlgHom : L →ₐ[K] ((L →ₐ[K] Ω) → Ω) where
  toFun l σ := σ l
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
  commutes' := by intro r; ext σ; simp

def tensorSepClosedAlgHom : (Ω ⊗[K] L) →ₐ[Ω] ((L →ₐ[K] Ω) → Ω) :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Ω _) (evalAlgHom K L Ω)

theorem algHom_linearIndependent :
    LinearIndependent Ω (fun (σ : L →ₐ[K] Ω) (l : L) => σ l) :=
  (linearIndependent_monoidHom L Ω).comp (fun σ => AlgHom.toRingHom σ |>.toMonoidHom)
    (fun _ _ heq => AlgHom.ext (MonoidHom.ext_iff.mp heq))

theorem column_functions_linearIndependent :
    LinearIndependent Ω
      (fun (i : Fin (finrank K L)) (φ : L →ₐ[K] Ω) => φ (finBasis K L i)) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  ·
    rw [← (span_flip_eq_top_iff_linearIndependent).mpr (algHom_linearIndependent K L Ω)]
    apply Submodule.span_le.mpr
    intro f ⟨l, hl⟩; rw [← hl]
    set b := finBasis K L
    have heq : (flip (fun (σ : L →ₐ[K] Ω) (l : L) => σ l)) l =
        ∑ i, (algebraMap K Ω (b.repr l i)) • (fun (φ : L →ₐ[K] Ω) => φ (b i)) := by
      ext φ; simp only [flip, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => rw [← b.sum_repr l, map_sum]
      congr 1; ext i; rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ·
    rw [Fintype.card_fin, finrank_pi_fintype, Finset.sum_const, finrank_self,
      smul_eq_mul, mul_one, Finset.card_univ]
    exact (algHom_card_eq_finrank_of_isSepClosed K L Ω).symm

theorem tensorSepClosedAlgHom_injective : Function.Injective (tensorSepClosedAlgHom K L Ω) := by
  set bΩ := Algebra.TensorProduct.basis Ω (finBasis K L)
  apply LinearMap.injective_of_linearIndependent (f := (tensorSepClosedAlgHom K L Ω).toLinearMap)
    (v := bΩ) (hv := bΩ.span_eq)

  have : (⇑(tensorSepClosedAlgHom K L Ω).toLinearMap ∘ ⇑bΩ) =
      (fun (i : Fin (finrank K L)) (φ : L →ₐ[K] Ω) => φ (finBasis K L i)) := by
    ext i φ
    simp [bΩ, Function.comp, AlgHom.toLinearMap_apply, Algebra.TensorProduct.basis_apply,
      tensorSepClosedAlgHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, evalAlgHom]
  rw [this]
  exact column_functions_linearIndependent K L Ω

theorem finrank_tensor_eq_finrank_pi_of_isSepClosed :
    finrank Ω (Ω ⊗[K] L) = finrank Ω ((L →ₐ[K] Ω) → Ω) := by
  rw [finrank_baseChange, finrank_pi_fintype, Finset.sum_const,
    finrank_self, smul_eq_mul, mul_one, Finset.card_univ, algHom_card_eq_finrank_of_isSepClosed]

theorem tensorSepClosedAlgHom_surjective : Function.Surjective (tensorSepClosedAlgHom K L Ω) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tensor_eq_finrank_pi_of_isSepClosed K L Ω) (f := (tensorSepClosedAlgHom K L Ω).toLinearMap)).mp
    (tensorSepClosedAlgHom_injective K L Ω)

theorem tensorSepClosedAlgHom_bijective : Function.Bijective (tensorSepClosedAlgHom K L Ω) :=
  ⟨tensorSepClosedAlgHom_injective K L Ω, tensorSepClosedAlgHom_surjective K L Ω⟩

def tensorSepClosedAlgEquiv : (Ω ⊗[K] L) ≃ₐ[Ω] ((L →ₐ[K] Ω) → Ω) :=
  AlgEquiv.ofBijective (tensorSepClosedAlgHom K L Ω) (tensorSepClosedAlgHom_bijective K L Ω)

end SepClosedDecomposition

end
