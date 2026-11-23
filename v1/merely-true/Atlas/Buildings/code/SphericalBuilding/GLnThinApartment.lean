/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLnInstance

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: every panel (codimension-$1$ face of a chamber) of an apartment frame $F$ extends
in exactly two ways to a chamber, yielding the thin-apartment axiom for the $\mathrm{GL}_n$ building. -/
structure PanelExtensionHyp where
  extend : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain)

/-- Converts a `PanelExtensionHyp` into the bundled `ThinApartmentHyp` consumed by the building
construction. -/
noncomputable def thinApartmentHyp
    (h : PanelExtensionHyp k n) : ThinApartmentHyp k n where
  extend_panel := fun F panel hcompat hlen => by
    obtain ⟨C₁, C₂, hch1, hch2, hne, hmem1, hmem2⟩ := h.extend F panel hcompat hlen
    exact ⟨C₁, C₂, hch1, hch2, hne, hmem1, hmem2, fun V hV => ⟨hmem1 V hV, hmem2 V hV⟩⟩

end GLnBuilding
