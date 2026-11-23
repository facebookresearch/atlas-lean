/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain
import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle

set_option linter.unusedVariables false

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: any finite list of proper subspaces of $k^n$ can be refined to a maximal
proper chain $V_0 < V_1 < \cdots < V_{n-1}$ of length $n-1$ containing all the original subspaces. -/
structure LatticeChainRefinementHyp where
  refine_via_chain : ∀ (subs : List (Submodule k (Vec k n))),
    (∀ V ∈ subs, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ (chain : List (Submodule k (Vec k n))),

      (∀ V ∈ subs, V ∈ chain) ∧

      chain.IsChain (· < ·) ∧

      chain.length = n - 1 ∧

      (∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤)

/-- Hypothesis: any complete strict flag of length $n-1$ of proper subspaces of $k^n$ extends
to a frame $F$ (decomposition into lines) compatible with every member of the flag. -/
structure FlagToFrameHyp where
  flag_to_frame : ∀ (chain : List (Submodule k (Vec k n))),
    chain.IsChain (· < ·) →
    chain.length = n - 1 →
    (∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ F : Frame k n, ∀ V ∈ chain, F.IsCompatible k n V

/-- Combining `LatticeChainRefinementHyp` and `FlagToFrameHyp` yields the simultaneous
refinement hypothesis: any finite collection of proper subspaces lies in a common apartment frame. -/
noncomputable def simultaneousRefinementHyp
    (hchain : LatticeChainRefinementHyp k n)
    (hframe : FlagToFrameHyp k n) : SimultaneousRefinementHyp k n where
  refine_list := fun subs hproper => by

    obtain ⟨chain, hcontains, hincr, hlen, hchain_proper⟩ :=
      hchain.refine_via_chain subs hproper

    obtain ⟨F, hF⟩ := hframe.flag_to_frame chain hincr hlen hchain_proper

    exact ⟨F, fun V hV => hF V (hcontains V hV)⟩

end GLnBuilding
