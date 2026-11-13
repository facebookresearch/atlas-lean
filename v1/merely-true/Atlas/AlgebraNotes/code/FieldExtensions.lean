/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace FieldExtensions

theorem tower_law (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [FiniteDimensional F E] [FiniteDimensional E K] :
    FiniteDimensional F K ∧ Module.finrank F K = Module.finrank F E * Module.finrank E K :=
  ⟨FiniteDimensional.trans F E K, (Module.finrank_mul_finrank F E K).symm⟩

theorem finiteDimensional_tower_iff (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E] :
    (Module.finrank K F * Module.finrank F E = Module.finrank K E) ∧
    (FiniteDimensional K E ↔ FiniteDimensional K F ∧ FiniteDimensional F E) := by
  refine ⟨Module.finrank_mul_finrank K F E, ?_⟩
  constructor
  · intro h
    exact ⟨FiniteDimensional.left K F E, FiniteDimensional.right K F E⟩
  · intro ⟨h1, h2⟩
    exact FiniteDimensional.trans K F E

theorem algebraic_operations {K L : Type*} [Field K] [Field L] [Algebra K L]
    {α β : L} (hα : IsAlgebraic K α) (hβ : IsAlgebraic K β) :
    IsAlgebraic K (α + β) ∧ IsAlgebraic K (α * β) ∧ IsAlgebraic K (α / β) :=
  ⟨hα.add hβ, hα.mul hβ, div_eq_mul_inv α β ▸ hα.mul (IsAlgebraic.inv_iff.mpr hβ)⟩

theorem isAlgebraic_def {K L : Type*} [Field K] [Field L] [Algebra K L] (α : L) :
    IsAlgebraic K α ↔ ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.aeval α p = 0 :=
  Iff.rfl

theorem isAlgebraic_iff_adjoin_finiteDimensional {K L : Type*} [Field K] [Field L]
    [Algebra K L] (α : L) :
    IsAlgebraic K α ↔ FiniteDimensional K ↥(IntermediateField.adjoin K {α}) := by
  rw [isAlgebraic_iff_isIntegral]
  constructor
  · exact IntermediateField.adjoin.finiteDimensional
  · intro h
    have hgen := IsIntegral.of_finite K (IntermediateField.AdjoinSimple.gen K α)
    have hcast : (algebraMap (↥(IntermediateField.adjoin K {α})) L)
        (IntermediateField.AdjoinSimple.gen K α) = α :=
      IntermediateField.AdjoinSimple.algebraMap_gen K α
    rw [← hcast]
    exact hgen.algebraMap
