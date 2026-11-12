/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two flags opposite to the same flag `F` necessarily share the same length. -/
theorem opposite_flags_same_len (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁)
    (h₂ : Flag.isOppositeFlag F F'₂) :
    F'₁.len = F'₂.len := by
  have := h₁.1; have := h₂.1; omega

/-- Codisjointness of opposite flags: each level `F.spaces i` together with the
matching level `F'.spaces (F'.len - 1 - i)` of the opposite flag spans `V`. -/
theorem isOppositeFlag_sup_eq_top (F F' : Flag k V) (h : Flag.isOppositeFlag F F')
    (i : Fin F.len) :
    let j : Fin F'.len := ⟨F'.len - 1 - i.val, by have := h.1; omega⟩
    F.spaces i ⊔ F'.spaces j = ⊤ := by
  obtain ⟨hlen, _, hcompl⟩ := h
  exact (hcompl hlen i).1

/-- Disjointness of opposite flags: each level `F.spaces i` and the matching level
`F'.spaces (F'.len - 1 - i)` of the opposite flag intersect trivially. -/
theorem isOppositeFlag_inf_eq_bot (F F' : Flag k V) (h : Flag.isOppositeFlag F F')
    (i : Fin F.len) :
    let j : Fin F'.len := ⟨F'.len - 1 - i.val, by have := h.1; omega⟩
    F.spaces i ⊓ F'.spaces j = ⊥ := by
  obtain ⟨hlen, _, hcompl⟩ := h
  exact (hcompl hlen i).2

end GeometricAlgebra
