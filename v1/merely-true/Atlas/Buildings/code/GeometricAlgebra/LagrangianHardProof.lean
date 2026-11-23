/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open FiniteDimensional Module Submodule

variable {k : Type*} [Field k]
  {V₁ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  {V₂ : Type*} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
  (W₂ : Submodule k V₂)

/-- Linear equivalence identifying the product submodule `⊤ × W₂ ⊆ V₁ × V₂` with
the external product `V₁ × W₂`. -/
noncomputable def prodTopLinearEquiv :
    (Submodule.prod (⊤ : Submodule k V₁) W₂ : Submodule k (V₁ × V₂)) ≃ₗ[k] V₁ × W₂ where
  toFun := fun ⟨⟨v₁, v₂⟩, hv⟩ => (v₁, ⟨v₂, (Submodule.mem_prod.mp hv).2⟩)
  invFun := fun ⟨v₁, ⟨w₂, hw₂⟩⟩ =>
    ⟨(v₁, w₂), Submodule.mem_prod.mpr ⟨Submodule.mem_top, hw₂⟩⟩
  left_inv := by
    rintro ⟨⟨v₁, v₂⟩, hv⟩
    simp
  right_inv := by
    rintro ⟨v₁, ⟨w₂, hw₂⟩⟩
    simp
  map_add' := by
    rintro ⟨⟨a₁, a₂⟩, ha⟩ ⟨⟨b₁, b₂⟩, hb⟩
    simp
  map_smul' := by
    rintro c ⟨⟨v₁, v₂⟩, hv⟩
    simp
