/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.StrongIsoExtHelper
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]

/-- The *$W$-valued distance* on a building: a function
$\delta : \mathrm{Cham}(X)^2 \to W$ taking values in a Coxeter group $W$, with
$\delta(C, C) = 1$, satisfying $\ell(\delta(C, D)) = d(C, D)$, and compatible
with the natural Coxeter labeling of each apartment via an isomorphism. -/
structure Building.WValuedDist (b : Building V) where
  S_idx : Type*
  [S_idx_dec : DecidableEq S_idx]
  [S_idx_fin : Fintype S_idx]
  coxeterMatrix : CoxeterMatrix S_idx
  delta : Finset V → Finset V → coxeterMatrix.Group
  delta_self : ∀ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C →
    delta C C = 1
  galleryDist_eq_length : ∀ (C D : Finset V),
    galleryDist b.toChamberComplex.toSimplicialComplex C D =
    coxeterMatrix.toCoxeterSystem.length (delta C D)

  delta_apt_compat : ∀ A ∈ b.apartmentSystem.apartments,
    ∀ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
    (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) →
    (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) →
    ∃ (iso : coxeterMatrix.Group ≃* M.Group),
      ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
        iso (delta C D) = (φ C)⁻¹ * (φ D)


/-- The $W$-valued distance from a fixed chamber $C$ is injective on chambers
of any apartment containing $C$. -/
lemma Building.WValuedDist.delta_injective_in_apt
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (δW : Building.WValuedDist b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C D₁ D₂ : Finset V)
    (hC_mem : C ∈ A.faces) (hC : A.IsMaximal C)
    (hD₁_mem : D₁ ∈ A.faces) (hD₁ : A.IsMaximal D₁)
    (hD₂_mem : D₂ ∈ A.faces) (hD₂ : A.IsMaximal D₂)
    (h_eq : δW.delta C D₁ = δW.delta C D₂) :
    D₁ = D₂ := by

  obtain ⟨B_idx, M, cc, hcc_eq, φ, hφ_inj, hφ_surj, _⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA

  obtain ⟨iso, hiso⟩ := δW.delta_apt_compat A hA B_idx M φ hφ_inj hφ_surj

  have h1 : iso (δW.delta C D₁) = (φ C)⁻¹ * (φ D₁) :=
    hiso C D₁ hC_mem hC hD₁_mem hD₁
  have h2 : iso (δW.delta C D₂) = (φ C)⁻¹ * (φ D₂) :=
    hiso C D₂ hC_mem hC hD₂_mem hD₂

  have h3 : (φ C)⁻¹ * (φ D₁) = (φ C)⁻¹ * (φ D₂) := by
    rw [← h1, ← h2, h_eq]

  have h4 : φ D₁ = φ D₂ := mul_left_cancel h3

  exact hφ_inj D₁ hD₁ D₂ hD₂ h4



/-- A *strong isometry* $f : Y \to f(Y)$ between sets of chambers is a
bijection that preserves the $W$-valued distance $\delta$. -/
def IsStrongIsometry {b : Building V} (δW : Building.WValuedDist b)
    (Y Z : Set (Finset V))
    (φ : Finset V → Finset V) : Prop :=
  (∀ C ∈ Y, φ C ∈ Z) ∧
  (∀ C ∈ Z, ∃ D ∈ Y, φ D = C) ∧
  (∀ C ∈ Y, ∀ D ∈ Y,
    δW.delta (φ C) (φ D) = δW.delta C D)


