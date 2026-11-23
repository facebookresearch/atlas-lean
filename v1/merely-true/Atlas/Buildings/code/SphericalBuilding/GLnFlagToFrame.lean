/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: from any maximal proper flag one can extract $n$ lines that span $k^n$
independently and are compatible with every subspace of the flag — i.e.\ an adapted basis. -/
structure BasisFromFlagHyp where
  extract : ∀ (chain : List (Submodule k (Vec k n))),
    chain.IsChain (· < ·) →
    chain.length = n - 1 →
    (∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ (lines : Fin n → Submodule k (Vec k n)),

      (∀ i, Module.finrank k (lines i) = 1) ∧

      iSupIndep lines ∧

      (⨆ i, lines i = ⊤) ∧

      (∀ V ∈ chain, ∃ S : Finset (Fin n), V = ⨆ j ∈ S, lines j)

/-- Package the extracted lines into a `Frame k n`, witnessing the flag-to-frame hypothesis. -/
noncomputable def flagToFrameOfBasis
    (hyp : BasisFromFlagHyp k n) : FlagToFrameHyp k n where
  flag_to_frame := fun chain hchain hlen hproper => by

    obtain ⟨lines, h_dim, h_indep, h_span, h_compat⟩ :=
      hyp.extract chain hchain hlen hproper

    let F : Frame k n :=
      { lines := lines
        one_dim := h_dim
        indep := h_indep
        spanning := h_span }


    exact ⟨F, fun V hV => h_compat V hV⟩

end GLnBuilding
