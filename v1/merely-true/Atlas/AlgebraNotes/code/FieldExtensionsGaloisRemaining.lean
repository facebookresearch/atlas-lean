/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace FieldExtensionsGalois

noncomputable def algebraicClosureInL (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IntermediateField K L := IntermediateField.mk
  { carrier := {α : L | IsAlgebraic K α}
    mul_mem' := fun ha hb => ha.mul hb
    one_mem' := isAlgebraic_one
    add_mem' := fun ha hb => ha.add hb
    zero_mem' := isAlgebraic_zero
    algebraMap_mem' := fun r => isAlgebraic_algebraMap r }
  (fun _ hx => IsAlgebraic.inv_iff.mpr hx)

theorem isSeparable_iff_minpoly_separable (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] :
    Algebra.IsSeparable F E ↔ ∀ α : E, (minpoly F α).Separable := by
  constructor
  · intro h α; exact Algebra.IsSeparable.isSeparable F α
  · intro h; exact ⟨fun α => h α⟩
