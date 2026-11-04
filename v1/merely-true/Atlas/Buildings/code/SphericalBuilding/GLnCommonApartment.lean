/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnInstance

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: any finite list of proper non-zero subspaces is simultaneously compatible
with some frame $F$ — i.e.\ admits a common adapted basis. -/
structure SimultaneousRefinementHyp where
  refine_list : ∀ (subs : List (Submodule k (Vec k n))),
    (∀ V ∈ subs, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ F : Frame k n, ∀ V ∈ subs, F.IsCompatible k n V

/-- From simultaneous refinement of arbitrary lists, deduce that any two flags lie in a
common apartment: apply the hypothesis to $\sigma.\mathrm{chain} \mathbin{+\!\!+} \tau.\mathrm{chain}$. -/
noncomputable def commonApartmentHyp
    (h : SimultaneousRefinementHyp k n) : CommonApartmentHyp k n where
  refine_flags := fun σ τ => by
    obtain ⟨F, hF⟩ := h.refine_list (σ.chain ++ τ.chain) (by
      intro V hV
      rw [List.mem_append] at hV
      cases hV with
      | inl hV => exact σ.chain_proper V hV
      | inr hV => exact τ.chain_proper V hV)
    exact ⟨F, fun V hV => hF V (List.mem_append.mpr (Or.inl hV)),
               fun V hV => hF V (List.mem_append.mpr (Or.inr hV))⟩

end GLnBuilding
