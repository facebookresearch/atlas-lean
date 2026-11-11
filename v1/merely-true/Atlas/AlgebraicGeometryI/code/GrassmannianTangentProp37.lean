/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod

noncomputable section

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- Grassmannian chart at `V` with complement `V'`: sends `φ : V → V'` to its graph in `W`. -/
def grassmannianChart (V V' : Submodule F W) (hc : IsCompl V V')
    (φ : V →ₗ[F] V') : Submodule F W :=
  (LinearMap.graph φ).map (Submodule.prodEquivOfIsCompl V V' hc).toLinearMap

/-- The chart maps the zero linear map to the basepoint `V` of the Grassmannian. -/
theorem grassmannianChart_zero (V V' : Submodule F W) (hc : IsCompl V V') :
    grassmannianChart V V' hc 0 = V := by
  ext w
  simp only [grassmannianChart, Submodule.mem_map, LinearMap.mem_graph_iff,
    LinearMap.zero_apply, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨⟨a, b⟩, hb, heq⟩
    change b = 0 at hb
    subst hb
    simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero] at heq
    rw [← heq]; exact a.2
  · intro hw
    exact ⟨⟨⟨w, hw⟩, 0⟩, rfl, by
      simp only [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]⟩

/-- Chart injectivity: distinct linear maps yield distinct graphs in `W`. -/
theorem grassmannianChart_injective (V V' : Submodule F W) (hc : IsCompl V V') :
    Function.Injective (grassmannianChart V V' hc) := by
  intro φ ψ h
  simp only [grassmannianChart] at h
  have hinj := (Submodule.prodEquivOfIsCompl V V' hc).injective
  have hgraph : LinearMap.graph φ = LinearMap.graph ψ :=
    Submodule.map_injective_of_injective hinj h
  ext v
  have hmem : (v, φ v) ∈ LinearMap.graph ψ :=
    hgraph ▸ (LinearMap.mem_graph_iff φ _).2 rfl
  exact congr_arg Subtype.val ((LinearMap.mem_graph_iff ψ _).1 hmem)

/-- Tangent-space isomorphism for the Grassmannian: `Hom(V, V') ≃ Hom(V, W / V)`. -/
def grassmannianTangentIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V)) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F V)
    (Submodule.quotientEquivOfIsCompl V V' hc).symm

/-- Cotangent-space isomorphism for the Grassmannian: `Hom(V', V) ≃ Hom(W / V, V)`. -/
def grassmannianCotangentIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V) :=
  LinearEquiv.arrowCongr (Submodule.quotientEquivOfIsCompl V V' hc).symm
    (LinearEquiv.refl F V)

/-- Prop 37 (Lec 20), tangent part: `T_V Gr ≃ Hom(V, W / V)`, expressed via the splitting `V'`. -/
theorem proposition_37_tangent_space (V V' : Submodule F W) (hc : IsCompl V V') :
    Nonempty ((V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V))) :=
  ⟨grassmannianTangentIso V V' hc⟩

/-- Prop 37 (Lec 20), cotangent part: `Ω_V Gr ≃ Hom(W / V, V)`. -/
theorem proposition_37_cotangent_space (V V' : Submodule F W) (hc : IsCompl V V') :
    Nonempty ((V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V)) :=
  ⟨grassmannianCotangentIso V V' hc⟩

/-- Comparison isomorphism between the tangent space at `V` computed via complement `V'₁` vs `V'₂`. -/
def grassmannianTangentIso_independence
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂) :
    (V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂) :=
  (grassmannianTangentIso V V'₁ h₁).trans (grassmannianTangentIso V V'₂ h₂).symm

/-- The tangent space identification does not depend on the choice of complement (Prop 37). -/
theorem proposition_37_complement_independence
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂) :
    Nonempty ((V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂)) :=
  ⟨grassmannianTangentIso_independence V V'₁ V'₂ h₁ h₂⟩

end
