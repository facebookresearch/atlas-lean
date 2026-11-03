/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.IsometryGroups

namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The standard isotropic flag complex of $(V, B)$: simplices are finite chains
$W_1 \le W_2 \le \cdots$ of totally isotropic subspaces with respect to the bilinear form $B$. -/
noncomputable def standardComplex (B : LinearMap.BilinForm k V) :
    IsotropicFlagComplex B where
  simplices := { σ : Finset (Submodule k V) |
    (∀ W ∈ σ, IsotropicSubspace B W) ∧
    (∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁) }
  simplex_isotropic := fun σ hσ W hW => hσ.1 W hW
  simplex_chain := fun σ hσ W₁ hW₁ W₂ hW₂ => hσ.2 W₁ hW₁ W₂ hW₂
  face_closed := fun σ hσ τ hτ_sub hτ_ne => by
    constructor
    · intro W hW; exact hσ.1 W (hτ_sub hW)
    · intro W₁ hW₁ W₂ hW₂; exact hσ.2 W₁ (hτ_sub hW₁) W₂ (hτ_sub hW₂)

/-- The standard apartments of the isometry building, indexed by hyperbolic frames of $(V,B)$ of
rank $n$. Each apartment carries the full set of isotropic chains as its simplices. -/
noncomputable def standardApartments (B : LinearMap.BilinForm k V) (n : ℕ) :
    Set (Apartment B n) :=
  Set.range fun (frame : HyperbolicFrame B n) =>
    { frame := frame
      simplices := { σ : Finset (Submodule k V) |
        (∀ W ∈ σ, IsotropicSubspace B W) ∧
        (∀ W₁ ∈ σ, ∀ W₂ ∈ σ, W₁ ≤ W₂ ∨ W₂ ≤ W₁) } }


/-- Hypothesis: for any two isotropic simplices $\sigma_1, \sigma_2$ in the standard complex,
there exists a standard apartment containing both. -/
structure CommonIsotropicApartmentHyp (B : LinearMap.BilinForm k V) (n : ℕ) where
  find_common : ∀ σ₁ ∈ (standardComplex B).simplices, ∀ σ₂ ∈ (standardComplex B).simplices,
    ∃ A ∈ standardApartments B n, σ₁ ∈ A.simplices ∧ σ₂ ∈ A.simplices

/-- Hypothesis: whenever two apartments $A_1, A_2$ share a chamber $C$, there is a bijection
$f : A_1 \to A_2$ of their simplices fixing every simplex in $A_1 \cap A_2$. -/
structure ApartmentExchangeHyp (B : LinearMap.BilinForm k V) (n : ℕ) where
  exchange : ∀ A₁ ∈ standardApartments B n, ∀ A₂ ∈ standardApartments B n,
    ∀ C ∈ A₁.simplices, C ∈ A₂.simplices →
    ∃ f : Finset (Submodule k V) → Finset (Submodule k V),
      Function.Bijective f ∧
      (∀ σ ∈ A₁.simplices, f σ ∈ A₂.simplices) ∧
      (∀ σ ∈ A₁.simplices ∩ A₂.simplices, f σ = σ)


/-- The isometry building: assembles `standardComplex` and `standardApartments` into an
`IsBuilding` structure, given the common-apartment and apartment-exchange hypotheses. -/
noncomputable def isometryIsBuilding
    (B : LinearMap.BilinForm k V) (n : ℕ)
    (h_common : CommonIsotropicApartmentHyp B n)
    (h_exchange : ApartmentExchangeHyp B n) :
    IsBuilding B n where
  complex := standardComplex B
  apartments := standardApartments B n
  apartment_subcomplex := by
    intro A hA


    obtain ⟨frame, rfl⟩ := hA
    intro σ hσ
    exact hσ
  common_apartment := h_common.find_common
  apartment_exchange := h_exchange.exchange

end IsometryBuilding
