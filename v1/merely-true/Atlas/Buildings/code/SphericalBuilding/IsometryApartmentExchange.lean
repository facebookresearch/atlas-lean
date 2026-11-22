/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance

namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Helper: in the isometry building, all standard apartments share the same set of simplices
(namely, all isotropic chains). -/
lemma standardApartments_simplices_eq (B : LinearMap.BilinForm k V) (n : ℕ)
    (A₁ : Apartment B n) (hA₁ : A₁ ∈ standardApartments B n)
    (A₂ : Apartment B n) (hA₂ : A₂ ∈ standardApartments B n) :
    A₁.simplices = A₂.simplices := by
  obtain ⟨frame₁, rfl⟩ := hA₁
  obtain ⟨frame₂, rfl⟩ := hA₂
  rfl

/-- Apartment exchange axiom for the isometry building: any two apartments sharing a chamber
admit a bijection of simplices fixing the common ones. The identity works because all standard
apartments coincide as simplicial sets. -/
noncomputable def apartmentExchangeHypInstance (B : LinearMap.BilinForm k V) (n : ℕ) :
    ApartmentExchangeHyp B n where
  exchange := by
    intro A₁ hA₁ A₂ hA₂ C hC₁ _hC₂
    have heq := standardApartments_simplices_eq B n A₁ hA₁ A₂ hA₂
    exact ⟨id, Function.bijective_id, fun σ hσ => heq ▸ hσ, fun σ _ => rfl⟩

end IsometryBuilding
