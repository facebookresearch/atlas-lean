/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Given the simultaneous refinement hypothesis, two chambers $\sigma, \tau$ admit a common
adapted frame, obtained by applying the refinement to the concatenated chain. -/
noncomputable def twoChamberFrameHyp
    (h : SimultaneousRefinementHyp k n) : TwoChamberFrameHyp k n where
  frame_of_two_chambers := fun σ τ _ _ => by
    obtain ⟨F, hF⟩ := h.refine_list (σ.chain ++ τ.chain) (by
      intro V hV
      rw [List.mem_append] at hV
      cases hV with
      | inl hV => exact σ.chain_proper V hV
      | inr hV => exact τ.chain_proper V hV)
    exact ⟨F, fun V hV => hF V (List.mem_append.mpr (Or.inl hV)),
               fun V hV => hF V (List.mem_append.mpr (Or.inr hV))⟩

end GLnBuilding
