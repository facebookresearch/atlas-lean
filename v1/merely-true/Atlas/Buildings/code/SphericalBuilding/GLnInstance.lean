/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLn

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis: every panel (codimension-1 flag) extends to two distinct chambers, both
containing the panel — i.e.\ the apartment is thin. -/
structure ThinApartmentHyp where
  extend_panel : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain ∧ V ∈ C₂.chain)

/-- Hypothesis: any two flags $\sigma,\tau$ lie inside the apartment of a common frame $F$. -/
structure CommonApartmentHyp where
  refine_flags : ∀ (σ τ : SubspaceFlag k n),
    ∃ F : Frame k n, (∀ V ∈ σ.chain, F.IsCompatible k n V) ∧
                      (∀ V ∈ τ.chain, F.IsCompatible k n V)

/-- Hypothesis: two apartments containing a common pair of chambers $C_1,C_2$ admit a
bijective compatibility-preserving map fixing every member of $C_1.\mathrm{chain}$ and
$C_2.\mathrm{chain}$. -/
structure ApartmentIsoHyp where
  iso_apartments : ∀ (F₁ F₂ : Frame k n) (C₁ C₂ : SubspaceFlag k n),
    IsChamber k n C₁ → IsChamber k n C₂ →
    (∀ V ∈ C₁.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₁.IsCompatible k n V) →
    (∀ V ∈ C₁.chain, F₂.IsCompatible k n V) →
    (∀ V ∈ C₂.chain, F₂.IsCompatible k n V) →
    ∃ f : Submodule k (Vec k n) → Submodule k (Vec k n),
      Function.Bijective f ∧
      (∀ V, F₁.IsCompatible k n V → F₂.IsCompatible k n (f V)) ∧
      (∀ V ∈ C₁.chain, f V = V) ∧
      (∀ V ∈ C₂.chain, f V = V)

/-- Assembling the three hypotheses (thin apartments, common apartment, apartment iso)
into the building structure for $\mathrm{GL}_n(k)$. -/
noncomputable def glnIsBuilding
    (h_thin : ThinApartmentHyp k n)
    (h_common : CommonApartmentHyp k n)
    (h_iso : ApartmentIsoHyp k n) : IsBuilding k n where
  apartment_thin := h_thin.extend_panel
  common_apartment := h_common.refine_flags
  apartment_iso := h_iso.iso_apartments

end GLnBuilding
