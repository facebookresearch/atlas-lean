/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnThinApartment

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis: a panel compatible with a frame $F$ admits two distinct frame-compatible
subspaces $W_1, W_2$, each extending the panel into a chamber. -/
structure GapAnalysisHyp where
  fill_gap : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ (W₁ W₂ : Submodule k (Vec k n)),

      W₁ ≠ W₂ ∧
      F.IsCompatible k n W₁ ∧
      F.IsCompatible k n W₂ ∧


      (∃ C₁ : SubspaceFlag k n,
        IsChamber k n C₁ ∧
        (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
        W₁ ∈ C₁.chain) ∧

      (∃ C₂ : SubspaceFlag k n,
        IsChamber k n C₂ ∧
        (∀ V ∈ panel.chain, V ∈ C₂.chain) ∧
        W₂ ∈ C₂.chain)


/-- Hypothesis: a panel compatible with a frame extends directly to two distinct chambers,
both containing every subspace of the panel. -/
structure DirectPanelExtensionHyp where
  extend : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain)

/-- Wrapper turning a `DirectPanelExtensionHyp` into a `PanelExtensionHyp`. -/
noncomputable def panelExtensionOfDirect
    (h : DirectPanelExtensionHyp k n) : PanelExtensionHyp k n where
  extend := h.extend

end GLnBuilding
